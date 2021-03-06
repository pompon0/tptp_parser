module ConvBin(main,
  isInteresting,isSimple,isAverage,pullAll,pullAllCNF,
  readProtoTar,saveProtoTar) where

import Lens.Micro((.~),(^.),(&))
import Data.ProtoLens.Labels()
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
import qualified Data.Set as Set

import Pred
import Lib
import qualified Proto.Tptp as T
import qualified Parser
import qualified Trace
import qualified Form

--inputFile = "http://cl-informatik.uibk.ac.at/cek/grzegorz/f.tgz"
inputFile = "https://storage.googleapis.com/tptp/tptp_sample.tgz"
inputFileCNF = "https://storage.googleapis.com/tptp/tptp_sample_cnf.tgz"
inputFileTestCNF = "https://storage.googleapis.com/tptp/tptp_test_cnf.tgz"

--inputFile = "http://localhost:8000/tptp_sample.tgz"
outputFile = "/tmp/f.tgz"

extractEntry :: Tar.Entry -> IO (String,String)
extractEntry entry = do
  let path = Tar.entryPath entry
  case Tar.entryContent entry of
    Tar.NormalFile x _ -> return (path, B8.unpack (B.toStrict x))
    _ -> fail (path ++ " - not a file")

pullEntries :: String -> IO [(String,String)]
pullEntries url = do
  req <- S.parseRequest url
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

pullAll = pullAndParse inputFile
pullAllCNF = pullAndParse inputFileCNF
pullTestCNF = pullAndParse inputFileTestCNF

pullAndParse :: String -> IO [(String,T.File)]
pullAndParse url = do
  let {
    eval (path,content) = do
      resOrErr <- Trace.evalIO (Parser.parse content);
      case resOrErr of
        Left errStack -> fail (path ++ "\n" ++ show errStack)
        Right res -> return (path,res);
  }
  pullEntries url >>= mapM eval

saveProtoTar :: Message a => [(String,a)] -> IO ()
saveProtoTar = saveEntries . fmap (fmap TextFormat.showMessage)

isInteresting :: (String,T.File) -> IO Bool
isInteresting (_,tptpFile) = do
  form <- assert (Form.fromProto tptpFile)
  let eqPreds = filter (\p -> case unwrap p of { PEq _ _ -> True; _ -> False }) (Form.preds form)
  return $ if length eqPreds == 0 then False else case form of {
    Form.Or [Form.Neg x,y] | x==y -> False;
    Form.Or [x,Form.Neg y] | x==y -> False;
    _ -> True;
  }

isSimple :: (String,T.File) -> IO Bool
isSimple = return.(`elem` simpleCases).fst

isAverage :: (String,T.File) -> IO Bool
isAverage = return.(`elem` averageCases).fst

main = killable $ do
  problems <- pullAll
  printE "problems pulled"
  saveProtoTar problems

simpleCases = Set.fromList [
  "f/l115_zfmisc_1",
  "f/l13_ordinal1",
  "f/l18_zfmisc_1",
  "f/l22_zfmisc_1",
  "f/l3_partfun1",
  "f/l42_zfmisc_1",
  "f/l80_enumset1",
  "f/l86_enumset1",
  "f/l98_xboole_1",
  "f/t100_relat_1",
  "f/t102_funct_1",
  "f/t102_xboole_1",
  "f/t105_xboole_1",
  "f/t106_relat_1",
  "f/t108_zfmisc_1",
  "f/t109_funct_1",
  "f/t109_zfmisc_1",
  "f/t10_tmap_1",
  "f/t10_zfmisc_1",
  "f/t113_xboole_1",
  "f/t114_relat_1",
  "f/t117_zfmisc_1",
  "f/t11_wellord1",
  "f/t11_zfmisc_1",
  "f/t121_zfmisc_1",
  "f/t123_zfmisc_1",
  "f/t12_relat_1",
  "f/t135_relat_1",
  "f/t13_zfmisc_1",
  "f/t14_lattices",
  "f/t14_relat_1",
  "f/t151_relat_1",
  "f/t152_relat_1",
  "f/t156_relat_1",
  "f/t157_relat_1",
  "f/t158_relat_1",
  "f/t159_relat_1",
  "f/t15_finset_1",
  "f/t15_lattices",
  "f/t15_xboole_1",
  "f/t16_setfam_1",
  "f/t16_zfmisc_1",
  "f/t173_relat_1",
  "f/t174_relat_1",
  "f/t176_relat_1",
  "f/t177_relat_1",
  "f/t178_relat_1",
  "f/t17_lattices",
  "f/t17_mcart_1",
  "f/t17_xboole_1",
  "f/t18_funct_1",
  "f/t18_lattices",
  "f/t18_mcart_1",
  "f/t18_tops_1",
  "f/t18_wellord1",
  "f/t19_funct_1",
  "f/t1_relat_1",
  "f/t1_setfam_1",
  "f/t1_subset_1",
  "f/t1_tops_1",
  "f/t1_tops_2",
  "f/t22_lattices",
  "f/t23_yellow_1",
  "f/t26_zfmisc_1",
  "f/t2_waybel_7",
  "f/t2_wellord1",
  "f/t2_xboole_1",
  "f/t2_zfmisc_1",
  "f/t30_enumset1",
  "f/t30_xboole_1",
  "f/t31_enumset1",
  "f/t31_funct_2",
  "f/t31_xboole_1",
  "f/t32_enumset1",
  "f/t32_partfun1",
  "f/t32_wellord1",
  "f/t33_enumset1",
  "f/t33_funct_1",
  "f/t34_enumset1",
  "f/t34_partfun1",
  "f/t35_enumset1",
  "f/t36_enumset1",
  "f/t36_xboole_1",
  "f/t37_enumset1",
  "f/t37_relat_1",
  "f/t38_enumset1",
  "f/t38_relat_1",
  "f/t38_setfam_1",
  "f/t39_enumset1",
  "f/t3_funct_1",
  "f/t3_relat_1",
  "f/t3_xboole_1",
  "f/t40_enumset1",
  "f/t40_zfmisc_1",
  "f/t41_enumset1",
  "f/t41_funct_3",
  "f/t42_enumset1",
  "f/t42_subset_1",
  "f/t42_zfmisc_1",
  "f/t43_enumset1",
  "f/t43_relat_1",
  "f/t43_zfmisc_1",
  "f/t44_enumset1",
  "f/t44_zfmisc_1",
  "f/t45_enumset1",
  "f/t45_relat_1",
  "f/t45_xboole_1",
  "f/t46_enumset1",
  "f/t46_funct_2",
  "f/t46_setfam_1",
  "f/t46_xboole_1",
  "f/t47_enumset1",
  "f/t47_zfmisc_1",
  "f/t48_enumset1",
  "f/t48_funct_1",
  "f/t48_subset_1",
  "f/t49_enumset1",
  "f/t49_funct_2",
  "f/t49_mcart_1",
  "f/t49_zfmisc_1",
  "f/t4_finset_1",
  "f/t4_setfam_1",
  "f/t50_enumset1",
  "f/t50_mcart_1",
  "f/t51_enumset1",
  "f/t51_funct_1",
  "f/t52_enumset1",
  "f/t52_relat_1",
  "f/t53_enumset1",
  "f/t54_enumset1",
  "f/t54_relat_1",
  "f/t55_enumset1",
  "f/t55_relat_1",
  "f/t55_relset_2",
  "f/t56_enumset1",
  "f/t56_xboole_1",
  "f/t57_enumset1",
  "f/t57_funct_1",
  "f/t58_zfmisc_1",
  "f/t59_enumset1",
  "f/t60_enumset1",
  "f/t60_partfun1",
  "f/t60_xboole_1",
  "f/t61_xboole_1",
  "f/t61_zfmisc_1",
  "f/t62_xboole_1",
  "f/t64_enumset1",
  "f/t64_relset_2",
  "f/t65_partfun1",
  "f/t66_enumset1",
  "f/t68_enumset1",
  "f/t68_relat_1",
  "f/t68_zfmisc_1",
  "f/t69_enumset1",
  "f/t6_ordinal1",
  "f/t6_partfun1",
  "f/t6_xboole_1",
  "f/t70_enumset1",
  "f/t72_enumset1",
  "f/t73_enumset1",
  "f/t73_funct_1",
  "f/t73_partfun1",
  "f/t73_relat_1",
  "f/t73_zfmisc_1",
  "f/t74_enumset1",
  "f/t75_enumset1",
  "f/t75_relat_1",
  "f/t76_enumset1",
  "f/t79_xboole_1",
  "f/t7_mcart_1",
  "f/t7_partfun1",
  "f/t7_xboole_0",
  "f/t7_xboole_1",
  "f/t81_relat_1",
  "f/t82_relat_1",
  "f/t82_zfmisc_1",
  "f/t86_xboole_1",
  "f/t87_enumset1",
  "f/t88_mcart_1",
  "f/t88_xboole_1",
  "f/t89_xboole_1",
  "f/t8_finset_1",
  "f/t8_relat_1",
  "f/t8_wellord1",
  "f/t8_zfmisc_1",
  "f/t90_xboole_1",
  "f/t92_mcart_1",
  "f/t94_relat_1",
  "f/t96_xboole_1",
  "f/t97_funct_2",
  "f/t97_relat_1",
  "f/t97_xboole_1",
  "f/t99_relat_1",
  "f/t9_finset_1",
  "f/t9_ordinal1",
  "f/t9_zfmisc_1"]

averageCases = [
  "f/t9_zfmisc_1",
  "f/t9_wellord1",
  "f/t9_tops_1",
  "f/t9_subset_1",
  "f/t9_partfun1",
  "f/t9_ordinal1",
  "f/t9_funct_2",
  "f/t9_finset_1",
  "f/t99_xboole_1",
  "f/t99_relat_1",
  "f/t98_zfmisc_1",
  "f/t98_relat_1",
  "f/t98_funct_2",
  "f/t98_funct_1",
  "f/t97_xboole_1",
  "f/t97_relat_1",
  "f/t97_funct_2",
  "f/t96_xboole_1",
  "f/t94_xboole_1",
  "f/t94_relat_1",
  "f/t94_funct_1",
  "f/t92_xboole_1",
  "f/t92_mcart_1",
  "f/t92_funct_2",
  "f/t91_mcart_1",
  "f/t90_xboole_1",
  "f/t8_zfmisc_1",
  "f/t8_xboole_1",
  "f/t8_wellord2",
  "f/t8_wellord1",
  "f/t8_tops_2",
  "f/t8_tops_1",
  "f/t8_relat_1",
  "f/t8_finset_1",
  "f/t8_enumset1",
  "f/t89_xboole_1",
  "f/t89_relat_1",
  "f/t89_mcart_1",
  "f/t88_xboole_1",
  "f/t88_mcart_1",
  "f/t87_xboole_1",
  "f/t87_enumset1",
  "f/t86_xboole_1",
  "f/t86_relat_1",
  "f/t86_mcart_1",
  "f/t86_funct_2",
  "f/t85_xboole_1",
  "f/t85_mcart_1",
  "f/t84_zfmisc_1",
  "f/t84_xboole_1",
  "f/t84_enumset1",
  "f/t83_relat_1",
  "f/t83_enumset1",
  "f/t82_zfmisc_1",
  "f/t82_xboole_1",
  "f/t82_relat_1",
  "f/t82_enumset1",
  "f/t81_xboole_1",
  "f/t81_relat_1",
  "f/t81_enumset1",
  "f/t80_zfmisc_1",
  "f/t80_xboole_1",
  "f/t7_zfmisc_1",
  "f/t7_xboole_1",
  "f/t7_xboole_0",
  "f/t7_wellord1",
  "f/t7_tex_2",
  "f/t7_relat_1",
  "f/t7_partfun1",
  "f/t7_mcart_1",
  "f/t7_enumset1",
  "f/t79_xboole_1",
  "f/t79_enumset1",
  "f/t78_xboole_1",
  "f/t78_enumset1",
  "f/t77_zfmisc_1",
  "f/t77_xboole_1",
  "f/t77_enumset1",
  "f/t76_zfmisc_1",
  "f/t76_xboole_1",
  "f/t76_funct_1",
  "f/t76_enumset1",
  "f/t75_xboole_1",
  "f/t75_relat_1",
  "f/t75_enumset1",
  "f/t74_xboole_1",
  "f/t74_relat_1",
  "f/t74_partfun1",
  "f/t74_enumset1",
  "f/t73_zfmisc_1",
  "f/t73_xboole_1",
  "f/t73_relat_1",
  "f/t73_partfun1",
  "f/t73_mcart_1",
  "f/t73_funct_1",
  "f/t73_enumset1",
  "f/t72_funct_1",
  "f/t72_enumset1",
  "f/t71_partfun1",
  "f/t70_partfun1",
  "f/t70_enumset1",
  "f/t6_zfmisc_1",
  "f/t6_xboole_1",
  "f/t6_xboole_0",
  "f/t6_setfam_1",
  "f/t6_pre_topc",
  "f/t6_partfun1",
  "f/t6_ordinal1",
  "f/t6_orders_2",
  "f/t6_enumset1",
  "f/t69_zfmisc_1",
  "f/t69_partfun1",
  "f/t69_enumset1",
  "f/t68_zfmisc_1",
  "f/t68_relat_1",
  "f/t68_enumset1",
  "f/t67_zfmisc_1",
  "f/t67_xboole_1",
  "f/t67_funct_2",
  "f/t66_xboole_1",
  "f/t66_enumset1",
  "f/t65_tops_2",
  "f/t65_partfun1",
  "f/t65_funct_2",
  "f/t64_zfmisc_1",
  "f/t64_relset_2",
  "f/t64_enumset1",
  "f/t63_mcart_1",
  "f/t62_xboole_1",
  "f/t62_relset_2",
  "f/t62_relat_1",
  "f/t61_zfmisc_1",
  "f/t61_xboole_1",
  "f/t60_xboole_1",
  "f/t60_tops_1",
  "f/t60_partfun1",
  "f/t60_mcart_1",
  "f/t60_enumset1",
  "f/t5_xboole_0",
  "f/t5_tops_2",
  "f/t5_tops_1",
  "f/t5_setfam_1",
  "f/t59_relat_1",
  "f/t59_enumset1",
  "f/t58_zfmisc_1",
  "f/t58_funct_2",
  "f/t57_zfmisc_1",
  "f/t57_funct_2",
  "f/t57_funct_1",
  "f/t57_enumset1",
  "f/t56_xboole_1",
  "f/t56_tops_1",
  "f/t56_enumset1",
  "f/t55_zfmisc_1",
  "f/t55_xboole_1",
  "f/t55_relset_2",
  "f/t55_relat_1",
  "f/t55_funct_1",
  "f/t55_enumset1",
  "f/t54_relat_1",
  "f/t54_mcart_1",
  "f/t54_funct_1",
  "f/t54_enumset1",
  "f/t53_enumset1",
  "f/t52_zfmisc_1",
  "f/t52_relat_1",
  "f/t52_funct_1",
  "f/t52_enumset1",
  "f/t51_funct_1",
  "f/t51_enumset1",
  "f/t50_mcart_1",
  "f/t50_enumset1",
  "f/t4_tops_1",
  "f/t4_tex_2",
  "f/t4_subset_1",
  "f/t4_setfam_1",
  "f/t4_funct_3",
  "f/t4_finset_1",
  "f/t4_enumset1",
  "f/t49_zfmisc_1",
  "f/t49_mcart_1",
  "f/t49_funct_2",
  "f/t49_enumset1",
  "f/t48_subset_1",
  "f/t48_partfun2",
  "f/t48_mcart_1",
  "f/t48_funct_1",
  "f/t48_enumset1",
  "f/t47_zfmisc_1",
  "f/t47_subset_1",
  "f/t47_funct_2",
  "f/t47_enumset1",
  "f/t46_xboole_1",
  "f/t46_subset_1",
  "f/t46_setfam_1",
  "f/t46_funct_2",
  "f/t46_enumset1",
  "f/t45_yellow_0",
  "f/t45_xboole_1",
  "f/t45_subset_1",
  "f/t45_relat_1",
  "f/t45_funct_1",
  "f/t45_enumset1",
  "f/t44_zfmisc_1",
  "f/t44_yellow_0",
  "f/t44_xboole_1",
  "f/t44_enumset1",
  "f/t43_zfmisc_1",
  "f/t43_xboole_1",
  "f/t43_relat_1",
  "f/t43_enumset1",
  "f/t42_zfmisc_1",
  "f/t42_subset_1",
  "f/t42_setfam_1",
  "f/t42_relat_1",
  "f/t42_funct_3",
  "f/t42_enumset1",
  "f/t41_subset_1",
  "f/t41_setfam_1",
  "f/t41_partfun1",
  "f/t41_funct_3",
  "f/t41_enumset1",
  "f/t40_zfmisc_1",
  "f/t40_relat_1",
  "f/t40_enumset1",
  "f/t3_zfmisc_1",
  "f/t3_yellow_6",
  "f/t3_xboole_1",
  "f/t3_relat_1",
  "f/t3_funct_1",
  "f/t3_enumset1",
  "f/t39_lattice3",
  "f/t39_enumset1",
  "f/t38_zfmisc_1",
  "f/t38_xboole_1",
  "f/t38_setfam_1",
  "f/t38_relat_1",
  "f/t38_mcart_1",
  "f/t38_enumset1",
  "f/t37_setfam_1",
  "f/t37_relat_1",
  "f/t37_mcart_1",
  "f/t37_enumset1",
  "f/t36_xboole_1",
  "f/t36_mcart_1",
  "f/t36_enumset1",
  "f/t35_setfam_1",
  "f/t35_ordinal1",
  "f/t35_mcart_1",
  "f/t35_enumset1",
  "f/t34_partfun1",
  "f/t34_mcart_1",
  "f/t34_enumset1",
  "f/t33_subset_1",
  "f/t33_funct_3",
  "f/t33_funct_2",
  "f/t33_funct_1",
  "f/t33_enumset1",
  "f/t32_wellord1",
  "f/t32_subset_1",
  "f/t32_partfun1",
  "f/t32_enumset1",
  "f/t31_xboole_1",
  "f/t31_tops_2",
  "f/t31_subset_1",
  "f/t31_setfam_1",
  "f/t31_funct_2",
  "f/t31_enumset1",
  "f/t30_xboole_1",
  "f/t30_enumset1",
  "f/t2_zfmisc_1",
  "f/t2_xboole_1",
  "f/t2_wellord1",
  "f/t2_waybel_7",
  "f/t2_tex_2",
  "f/t2_relset_1",
  "f/t2_pre_topc",
  "f/t29_tops_2",
  "f/t29_subset_1",
  "f/t29_enumset1",
  "f/t28_xboole_1",
  "f/t28_partfun1",
  "f/t28_enumset1",
  "f/t27_yellow_1",
  "f/t27_enumset1",
  "f/t26_zfmisc_1",
  "f/t26_relat_1",
  "f/t26_orders_2",
  "f/t26_enumset1",
  "f/t25_subset_1",
  "f/t25_relat_1",
  "f/t24_tops_1",
  "f/t24_subset_1",
  "f/t24_mcart_1",
  "f/t24_funct_3",
  "f/t24_enumset1",
  "f/t23_yellow_1",
  "f/t23_enumset1",
  "f/t22_zfmisc_1",
  "f/t22_xboole_1",
  "f/t22_wellord1",
  "f/t22_subset_1",
  "f/t22_partfun1",
  "f/t22_lattices",
  "f/t22_enumset1",
  "f/t21_zfmisc_1",
  "f/t21_xboole_1",
  "f/t21_wellord2",
  "f/t21_wellord1",
  "f/t21_subset_1",
  "f/t21_enumset1",
  "f/t20_zfmisc_1",
  "f/t20_xboole_1",
  "f/t20_wellord2",
  "f/t20_wellord1",
  "f/t20_tmap_1",
  "f/t20_subset_1",
  "f/t20_setfam_1",
  "f/t20_enumset1",
  "f/t1_zfmisc_1",
  "f/t1_tops_2",
  "f/t1_tops_1",
  "f/t1_subset_1",
  "f/t1_setfam_1",
  "f/t1_relat_1",
  "f/t1_lattice3",
  "f/t1_funct_3",
  "f/t19_zfmisc_1",
  "f/t19_xboole_1",
  "f/t19_wellord2",
  "f/t19_waybel_9",
  "f/t19_ordinal1",
  "f/t19_funct_1",
  "f/t18_wellord1",
  "f/t18_tops_1",
  "f/t18_setfam_1",
  "f/t18_relset_1",
  "f/t18_mcart_1",
  "f/t18_lattices",
  "f/t18_funct_1",
  "f/t18_enumset1",
  "f/t184_relat_1",
  "f/t17_zfmisc_1",
  "f/t17_xboole_1",
  "f/t17_tops_2",
  "f/t17_subset_1",
  "f/t17_relat_1",
  "f/t17_mcart_1",
  "f/t17_lattices",
  "f/t17_enumset1",
  "f/t177_relat_1",
  "f/t176_relat_1",
  "f/t174_relat_1",
  "f/t173_relat_1",
  "f/t172_relat_1",
  "f/t16_zfmisc_1",
  "f/t16_subset_1",
  "f/t16_setfam_1",
  "f/t16_relset_1",
  "f/t16_relat_1",
  "f/t16_partfun1",
  "f/t16_ordinal1",
  "f/t16_mcart_1",
  "f/t16_enumset1",
  "f/t166_relat_1",
  "f/t164_relat_1",
  "f/t163_relat_1",
  "f/t162_relat_1",
  "f/t161_relat_1",
  "f/t15_zfmisc_1",
  "f/t15_xboole_1",
  "f/t15_tops_2",
  "f/t15_relset_1",
  "f/t15_relat_1",
  "f/t15_partfun1",
  "f/t15_mcart_1",
  "f/t15_lattices",
  "f/t15_finset_1",
  "f/t15_enumset1",
  "f/t159_relat_1",
  "f/t158_relat_1",
  "f/t157_relat_1",
  "f/t156_relat_1",
  "f/t153_relat_1",
  "f/t152_relat_1",
  "f/t151_relat_1",
  "f/t150_relat_1",
  "f/t14_zfmisc_1",
  "f/t14_xboole_1",
  "f/t14_tops_2",
  "f/t14_setfam_1",
  "f/t14_relat_1",
  "f/t14_mcart_1",
  "f/t14_lattices",
  "f/t14_enumset1",
  "f/t13_zfmisc_1",
  "f/t13_relset_2",
  "f/t13_mcart_1",
  "f/t139_relat_1",
  "f/t138_zfmisc_1",
  "f/t137_zfmisc_1",
  "f/t135_relat_1",
  "f/t134_relat_1",
  "f/t132_zfmisc_1",
  "f/t132_relat_1",
  "f/t130_zfmisc_1",
  "f/t12_zfmisc_1",
  "f/t12_xboole_1",
  "f/t12_relat_1",
  "f/t12_pre_topc",
  "f/t12_partfun1",
  "f/t12_ordinal1",
  "f/t12_mcart_1",
  "f/t12_enumset1",
  "f/t129_relat_1",
  "f/t128_zfmisc_1",
  "f/t123_zfmisc_1",
  "f/t122_zfmisc_1",
  "f/t121_relat_1",
  "f/t11_zfmisc_1",
  "f/t11_wellord2",
  "f/t11_wellord1",
  "f/t11_tops_1",
  "f/t11_funct_3",
  "f/t11_enumset1",
  "f/t119_zfmisc_1",
  "f/t119_relat_1",
  "f/t117_zfmisc_1",
  "f/t117_xboole_1",
  "f/t116_zfmisc_1",
  "f/t114_xboole_1",
  "f/t114_relat_1",
  "f/t113_zfmisc_1",
  "f/t113_xboole_1",
  "f/t113_relat_1",
  "f/t113_funct_2",
  "f/t111_xboole_1",
  "f/t111_relat_1",
  "f/t10_zfmisc_1",
  "f/t10_xboole_1",
  "f/t10_tops_2",
  "f/t10_tops_1",
  "f/t10_tmap_1",
  "f/t10_partfun1",
  "f/t10_enumset1",
  "f/t109_zfmisc_1",
  "f/t109_funct_1",
  "f/t108_zfmisc_1",
  "f/t108_xboole_1",
  "f/t108_relat_1",
  "f/t108_funct_1",
  "f/t107_xboole_1",
  "f/t107_funct_1",
  "f/t106_zfmisc_1",
  "f/t106_relat_1",
  "f/t105_zfmisc_1",
  "f/t105_xboole_1",
  "f/t102_xboole_1",
  "f/t102_funct_1",
  "f/t101_zfmisc_1",
  "f/t100_relat_1",
  "f/l9_yellow_6",
  "f/l98_xboole_1",
  "f/l97_xboole_1",
  "f/l86_enumset1",
  "f/l84_partfun1",
  "f/l83_partfun1",
  "f/l80_enumset1",
  "f/l55_tmap_1",
  "f/l48_subset_1",
  "f/l46_funct_1",
  "f/l45_tops_1",
  "f/l42_zfmisc_1",
  "f/l40_tex_2",
  "f/l3_partfun1",
  "f/l2_subset_1",
  "f/l28_zfmisc_1",
  "f/l24_zfmisc_1",
  "f/l22_zfmisc_1",
  "f/l20_zfmisc_1",
  "f/l1_zfmisc_1",
  "f/l18_zfmisc_1",
  "f/l186_relat_1",
  "f/l13_ordinal1",
  "f/l115_zfmisc_1"]
