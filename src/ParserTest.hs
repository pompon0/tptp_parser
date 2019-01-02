{-# LANGUAGE OverloadedLabels #-}
module ParserTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase,assertFailure,assertBool,(@=?))

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
import Data.Either

import qualified Parser
import qualified Trace
import qualified Form

tests = testGroup "ParserTest" [ testCase "mizar" mizar ]

inputFile = "http://cl-informatik.uibk.ac.at/cek/grzegorz/f.tgz"
outputFile = "/tmp/f.tgz"

parseTest :: Tar.Entry -> IO Tar.Entry
parseTest entry = do
  let path = Tar.entryPath entry
  case Tar.entryContent entry of
    Tar.NormalFile x _ -> do
      resOrErr <- Trace.evalIO (Parser.parse (B8.unpack $ B.toStrict x))
      case resOrErr of
        Left errStack -> assertFailure (path ++ " - " ++ show errStack)
        Right res -> do
          -- let formulas = map (\i -> i^. #formula) (res^. #input)
          -- mapM (\f -> putStrLn $ show $ Form.fromProto $ f) formulas
          putStrLn (path ++ " - OK")
          return $ Tar.Entry.fileEntry (Tar.Entry.entryTarPath entry) (BU.fromString $ TextFormat.showMessage res)
    _ -> assertFailure (path ++ " - not a file")

mizar = do
  req <- S.parseRequest inputFile
  resp <- S.httpBS req
  let entriesStream = Tar.read (GZip.decompress $ B.fromStrict $ S.getResponseBody resp)
  case Tar.foldlEntries (\a e -> e:a) [] entriesStream of
    Left (e,a) -> assertFailure (show e)
    Right entries -> do
      outEntries <- mapM parseTest entries
      B.writeFile outputFile $ GZip.compress $ Tar.write outEntries
