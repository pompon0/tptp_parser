proto_library(
    name = "tptp_proto",
    srcs = ["tptp.proto"],
    visibility = ["//visibility:public"],
)

proto_library(
    name = "solutions_proto",
    srcs = ["solutions.proto"],
    visibility = ["//visibility:public"],
    deps = [":tptp_proto"],
)

proto_library(
    name = "proof_proto",
    srcs = ["proof.proto"],
    visibility = ["//visibility:public"],
)
