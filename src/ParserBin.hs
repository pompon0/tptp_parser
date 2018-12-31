module ParserBin(main) where

import qualified Trace
import qualified Parser
import Data.Either

main = do
  input <- getContents
  print input
  resOrErr <- Trace.evalIO (Parser.parse input)
  case resOrErr of
    Left errStack -> do
      putStrLn ":: ERROR ::"
      mapM_ putStrLn errStack
    Right res -> print res 
