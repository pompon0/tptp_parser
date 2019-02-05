import qualified Data.ProtoLens.Setup as Setup
import Distribution.Simple as Simple

myHooks hooks = hooks {
  Simple.buildHook = \p l h f -> putStrLn "-- my build hook --" >> Simple.buildHook hooks p l h f
}

protoHooks = (Setup.generatingProtos "proto" Simple.simpleUserHooks)
main = Simple.defaultMainWithHooks $ myHooks $ protoHooks

