load("//:hs.bzl","hs_stack_binaries")

hs_stack_binaries(
  name = "tptp-parser",
  stack_yaml = "stack.yaml",
  srcs = glob([
    "src/**/*.hs",
    "bin/*.hs",
    "Setup.hs",
    "tptp-parser.cabal",
    "package.yaml",
  ]),
  protos = [
    "//proto:tptp_proto",
    "//proto:proof_proto",
  ],
  bins = ["checker","conv","thread","parser"],
  visibility = ["//visibility:public"],
)

