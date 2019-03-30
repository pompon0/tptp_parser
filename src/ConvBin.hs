module ConvBin(main,
  pullInteresting,pullSimple,
  readProtoTar,saveProtoTar) where

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

pullSimple = pullInteresting >>= filterM (return.(`elem` simpleCases).fst)

main = killable $ do
  problems <- pullInteresting
  printE "problems pulled"
  saveProtoTar problems

simpleCases = [
  "f/t9_ordinal1",
  "f/t97_xboole_1",
  "f/t97_relat_1",
  "f/t97_funct_2",
  "f/t96_xboole_1",
  "f/t92_mcart_1",
  "f/t90_xboole_1",
  "f/t8_wellord1",
  "f/t8_relat_1",
  "f/t89_xboole_1",
  "f/t88_xboole_1",
  "f/t88_mcart_1",
  "f/t86_xboole_1",
  "f/t81_relat_1",
  "f/t7_xboole_0",
  "f/t7_mcart_1",
  "f/t74_enumset1",
  "f/t73_zfmisc_1",
  "f/t72_enumset1",
  "f/t70_enumset1",
  "f/t6_xboole_1",
  "f/t6_ordinal1",
  "f/t69_enumset1",
  "f/t68_zfmisc_1",
  "f/t68_enumset1",
  "f/t64_relset_2",
  "f/t61_zfmisc_1",
  "f/t61_xboole_1",
  "f/t60_partfun1",
  "f/t56_enumset1",
  "f/t55_enumset1",
  "f/t54_relat_1",
  "f/t54_enumset1",
  "f/t53_enumset1",
  "f/t52_relat_1",
  "f/t52_enumset1",
  "f/t51_enumset1",
  "f/t50_enumset1",
  "f/t4_setfam_1",
  "f/t4_finset_1",
  "f/t49_mcart_1",
  "f/t49_funct_2",
  "f/t49_enumset1",
  "f/t48_enumset1",
  "f/t47_zfmisc_1",
  "f/t47_enumset1",
  "f/t46_xboole_1",
  "f/t46_setfam_1",
  "f/t46_enumset1",
  "f/t45_xboole_1",
  "f/t45_relat_1",
  "f/t45_enumset1",
  "f/t44_zfmisc_1",
  "f/t44_enumset1",
  "f/t43_zfmisc_1",
  "f/t43_relat_1",
  "f/t43_enumset1",
  "f/t42_zfmisc_1",
  "f/t42_enumset1",
  "f/t41_enumset1",
  "f/t40_zfmisc_1",
  "f/t40_enumset1",
  "f/t3_xboole_1",
  "f/t39_enumset1",
  "f/t38_enumset1",
  "f/t37_enumset1",
  "f/t36_enumset1",
  "f/t35_enumset1",
  "f/t34_partfun1",
  "f/t34_enumset1",
  "f/t32_wellord1",
  "f/t31_xboole_1",
  "f/t31_funct_2",
  "f/t31_enumset1",
  "f/t30_xboole_1",
  "f/t2_xboole_1",
  "f/t1_subset_1",
  "f/t1_setfam_1",
  "f/t1_relat_1",
  "f/t174_relat_1",
  "f/t16_zfmisc_1",
  "f/t15_xboole_1",
  "f/t15_finset_1",
  "f/t157_relat_1",
  "f/t156_relat_1",
  "f/t13_zfmisc_1",
  "f/t135_relat_1",
  "f/t12_relat_1",
  "f/t123_zfmisc_1",
  "f/t11_wellord1",
  "f/t117_zfmisc_1",
  "f/t114_relat_1",
  "f/t113_xboole_1",
  "f/t10_tmap_1",
  "f/t108_zfmisc_1",
  "f/t106_relat_1",
  "f/t105_xboole_1",
  "f/t102_xboole_1",
  "f/l98_xboole_1",
  "f/l115_zfmisc_1",
  "f/t8_zfmisc_1",
  "f/t87_enumset1",
  "f/t76_enumset1",
  "f/t75_enumset1",
  "f/t73_enumset1",
  "f/t66_enumset1",
  "f/t64_enumset1",
  "f/t62_xboole_1",
  "f/t60_enumset1",
  "f/t59_enumset1",
  "f/t57_enumset1",
  "f/t55_relset_2",
  "f/t55_relat_1",
  "f/t50_mcart_1",
  "f/t3_relat_1",
  "f/t37_relat_1",
  "f/t33_enumset1",
  "f/t32_enumset1",
  "f/t30_enumset1",
  "f/t2_waybel_7",
  "f/t26_zfmisc_1",
  "f/t19_funct_1",
  "f/t173_relat_1",
  "f/t14_relat_1",
  "f/t109_zfmisc_1",
  "f/l86_enumset1",
  "f/l80_enumset1",
  "f/l3_partfun1"]

