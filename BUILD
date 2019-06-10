load("//:hs.bzl","hs_stack_binaries")

hs_stack_binaries(
  name = "tptp-parser",
  srcs = glob([
    "src/**/*.hs",
    "bin/*.hs",
    "Setup.hs",
    "stack.yaml",
    "tptp-parser.cabal",
    "package.yaml",
  ]),
  protos = [
    "//proto:tptp_proto",
    "//proto:proof_proto",
  ],
  bins = ["checker","conv","thread","parser"],
)

