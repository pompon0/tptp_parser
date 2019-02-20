module ConvBin(main,pullInteresting,readProtoTar,saveProtoTar) where

import Lens.Micro((.~),(^.),(&))
import Lens.Labels.Unwrapped ()
import qualified Network.HTTP.Simple as S
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy.UTF8 as BU
import qualified Codec.Archive.Tar as Tar
import qualified Codec.Archive.Tar.Entry as Tar.Entry
import qualified Codec.Compression.GZip as GZip 
import qualified Data.ProtoLens.TextFormat as TextFormat
import Data.ProtoLens.Message(Message)
import Data.Either
import qualified Data.Text.Lazy as Text
import qualified Data.Map as Map
import Control.Monad(filterM)

import Lib
import qualified Proto.Tptp as T
import qualified Parser
import qualified Trace
import qualified Form

--inputFile = "http://cl-informatik.uibk.ac.at/cek/grzegorz/f.tgz"
inputFile = "https://storage.googleapis.com/tptp/tptp_sample.tgz"
outputFile = "/tmp/f.tgz"

extractEntry :: Tar.Entry -> IO (String,String)
extractEntry entry = do
  let path = Tar.entryPath entry
  case Tar.entryContent entry of
    Tar.NormalFile x _ -> return (path, B8.unpack (B.toStrict x))
    _ -> fail (path ++ " - not a file")

pullEntries :: IO [(String,String)]
pullEntries = do
  req <- S.parseRequest inputFile
  resp <- S.httpBS req
  let entriesStream = Tar.read (GZip.decompress $ B.fromStrict $ S.getResponseBody resp)
  case Tar.foldlEntries (\a e -> e:a) [] entriesStream of
    Left (e,a) -> fail (show e)
    Right entries -> mapM extractEntry entries

readEntries :: String -> IO [(String,String)]
readEntries path = do
  tarRaw <- B.readFile path
  let entriesStream = Tar.read (GZip.decompress tarRaw)
  case Tar.foldlEntries (\a e -> e:a) [] entriesStream of
    Left (e,a) -> fail (show e)
    Right entries -> mapM extractEntry entries

makeEntry :: (String,String) -> IO Tar.Entry
makeEntry (path,content) = do
  case Tar.Entry.toTarPath False path of
    Left errMsg -> fail errMsg
    Right tarPath -> return $ Tar.Entry.fileEntry tarPath (BU.fromString content)

saveEntries :: [(String,String)] -> IO ()
saveEntries entries = do
  outEntries <- mapM makeEntry entries
  B.writeFile outputFile $ GZip.compress $ Tar.write outEntries

readProtoTar :: Message a => String -> IO [(String,a)]
readProtoTar path = readEntries path >>= mapM (
  \(k,v) -> case TextFormat.readMessage (Text.pack v) of
    Left err -> fail $ "error while parsing " ++ k ++ ": " ++ err
    Right proto -> return (k,proto))

pullProtoTar :: IO [(String,T.File)]
pullProtoTar = do
  let {
    eval (path,content) = do
      resOrErr <- Trace.evalIO (Parser.parse content);
      case resOrErr of
        Left errStack -> fail (path ++ "\n" ++ show errStack)
        Right res -> return (path,res);
  }
  pullEntries >>= mapM eval

saveProtoTar :: Message a => [(String,a)] -> IO ()
saveProtoTar = saveEntries . fmap (fmap TextFormat.showMessage)

interesting :: T.File -> IO Bool
interesting tptpFile = do
  form <- assert (Form.fromProto tptpFile)
  let eqPreds = filter (\p -> case p of { Form.PEq _ _ -> True; _ -> False }) (Form.preds form)
  return $ if length eqPreds == 0 then False else case form of {
    Form.Or [Form.Neg x,y] | x==y -> False;
    Form.Or [x,Form.Neg y] | x==y -> False;
    _ -> True;
  }

pullInteresting = pullProtoTar >>= filterM (interesting.snd)

main = pullInteresting >>= saveProtoTar
