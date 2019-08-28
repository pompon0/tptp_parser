proto_library(
    name = "tptp_proto",
    srcs = ["tptp.proto"],
    visibility = ["//visibility:public"],
    strip_import_prefix = "//proto",
)

proto_library(
    name = "solutions_proto",
    srcs = ["solutions.proto"],
    visibility = ["//visibility:public"],
    deps = [":tptp_proto"],
    strip_import_prefix = "//proto",
)

proto_library(
    name = "proof_proto",
    srcs = ["proof.proto"],
    visibility = ["//visibility:public"],
    strip_import_prefix = "//proto",
)

load("@rules_haskell//haskell:protobuf.bzl", "haskell_proto_library")

haskell_proto_library(
  name = "tptp_haskell_proto",
  deps = ["//proto:tptp_proto"],
  visibility = ["//visibility:public"],
)

haskell_proto_library(
  name = "proof_haskell_proto",
  deps = ["//proto:proof_proto"],
  visibility = ["//visibility:public"],
)

haskell_proto_library(
  name = "solutions_haskell_proto",
  deps = ["//proto:solutions_proto"],
  visibility = ["//visibility:public"],
)
