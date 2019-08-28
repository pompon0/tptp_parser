load("@rules_haskell//haskell:cabal.bzl", "haskell_cabal_binary")

haskell_cabal_binary(
  name = "proto-lens-protoc",
  srcs = glob(["**"]),
  version = "0.5.0.0",
  deps = [
    "@stackage//:base",
    "@stackage//:bytestring",
    "@stackage//:containers",
    "@stackage//:haskell-src-exts",
    "@stackage//:lens-family",
    "@stackage//:proto-lens",
    "@stackage//:text",
  ],
  visibility = ["//visibility:public"],
)
