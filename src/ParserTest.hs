module ParserTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase,assertFailure,assertBool,(@=?))

import qualified Network.HTTP.Simple as S
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Char8 as B8
import qualified Codec.Archive.Tar as Tar
import qualified Codec.Archive.Tar.Entry as Tar.Entry
import qualified Codec.Compression.GZip as GZip 

import Data.Either
import qualified Parser
import qualified Trace

tests = testGroup "ParserTest" [ testCase "mizar" mizar ]

parseTest :: Tar.Entry -> IO ()
parseTest entry = do
  let path = Tar.entryPath entry
  case Tar.entryContent entry of
    Tar.NormalFile x _ -> do
      resOrErr <- Trace.evalIO (Parser.parse (B8.unpack $ B.toStrict x))
      case resOrErr of
        Left errStack -> putStrLn (path ++ " - " ++ show errStack) 
        Right res -> putStrLn (path ++ " - OK")
    _ -> putStrLn (path ++ " - not a file")

mizar = do
  req <- S.parseRequest "http://cl-informatik.uibk.ac.at/cek/grzegorz/f.tgz"
  resp <- S.httpBS req
  let entriesStream = Tar.read (GZip.decompress $ B.fromStrict $ S.getResponseBody resp)
  case Tar.foldlEntries (\a e -> e:a) [] entriesStream of
    Left (e,a) -> assertFailure (show e)
    Right entries -> mapM_ parseTest entries
