load("@rules_haskell//haskell:defs.bzl", "haskell_binary")

haskell_binary(
  name = "checker",
  srcs = ["checker.hs"],
  deps = [
    "@stackage//:base",
    "//src:tptp-parser"
  ],
)
