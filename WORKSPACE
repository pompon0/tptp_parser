workspace(name="tptp_parser")

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

skylib_version = "0.8.0"
http_archive(
  name = "bazel_skylib",
  type = "tar.gz",
  url = "https://github.com/bazelbuild/bazel-skylib/releases/download/{}/bazel-skylib.{}.tar.gz".format (skylib_version, skylib_version),
  sha256 = "2ef429f5d7ce7111263289644d233707dba35e39696377ebab8b0bc701f7818e",
)

http_archive(
  name = "com_google_protobuf",
  strip_prefix = "protobuf-3.9.0",
  urls = ["https://github.com/google/protobuf/archive/v3.9.0.zip"],
)
load("@com_google_protobuf//:protobuf_deps.bzl","protobuf_deps")
protobuf_deps()

###################################

http_archive(
  name = "rules_haskell",
  strip_prefix = "rules_haskell-master",
  urls = ["https://github.com/pompon0/rules_haskell/archive/master.tar.gz"],
)

load("@rules_haskell//haskell:repositories.bzl", "rules_haskell_dependencies", "rules_haskell_toolchains")
rules_haskell_dependencies()
rules_haskell_toolchains()

http_archive(
  name = "happy",
  strip_prefix = "happy-1.19.10",
  urls = ["http://hackage.haskell.org/package/happy-1.19.10/happy-1.19.10.tar.gz"],
  sha256 = "22eb606c97105b396e1c7dc27e120ca02025a87f3e44d2ea52be6a653a52caed",
  build_file = "//:third_party/happy.BUILD",
)

load("@rules_haskell//haskell:cabal.bzl", "stack_snapshot")

stack_snapshot(
  name = "stackage",
  packages = [
    "base",
    "data-default-class",
    "haskell-src-exts",
    "either",
    "tasty-hunit",
    "tasty",
    "parsec",
    "transformers",
    "unix",
    "bytestring",
    "utf8-string",
    "tar",
    "http-conduit",
    "zlib",
    "lens",
    "proto-lens-runtime",
    "proto-lens",
    "microlens",
    "lens-family",
    "text",
    "containers",
    "mtl",
    "MissingH",
    "threads",
    "concurrent-extra",
    "unbounded-delays",
    "deepseq",
    "split",
    "data-ordlist",
    "clock",
    "hashable",
    "hashtables",
    "options",
    "array",
    "vector",
  ],
  snapshot = "lts-14.2",
  tools = ["@happy"],
)

http_archive(
  name = "set-monad",
  strip_prefix = "set-monad-master",
  urls = ["https://github.com/giorgidze/set-monad/archive/master.zip"],
  build_file = "//:third_party/set-monad.BUILD",
)

http_archive(
  name = "proto-lens-protoc",
  urls = ["http://hackage.haskell.org/package/proto-lens-protoc-0.5.0.0/proto-lens-protoc-0.5.0.0.tar.gz"],
  build_file = "//:third_party/proto-lens-protoc.BUILD",
  strip_prefix = "proto-lens-protoc-0.5.0.0",
)

register_toolchains(":protobuf-toolchain")
