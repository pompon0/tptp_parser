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

'''http_archive(
  name = "io_tweag_rules_haskell",
  sha256 = "a19bb160ed6a02574a5ba8d44ac1797991f4ecc2aa34387ab568a05621f2e64a",
  strip_prefix = "rules_haskell-master",
  urls = ["https://github.com/tweag/rules_haskell/archive/master.tar.gz"],
)

load("@io_tweag_rules_haskell//haskell:repositories.bzl","haskell_repositories")
haskell_repositories()
load("@io_tweag_rules_haskell//haskell:haskell.bzl","haskell_register_ghc_bindists","haskell_register_toolchains")
# haskell_register_ghc_bindists(version = "8.6.4")
haskell_register_toolchains(version = "8.6.4")

load("@io_tweag_rules_haskell//tools:os_info.bzl", "os_info")
os_info(name = "os_info")

http_archive(
  name = "ai_formation_hazel",
  sha256 = "a19bb160ed6a02574a5ba8d44ac1797991f4ecc2aa34387ab568a05621f2e64a",
  strip_prefix = "rules_haskell-master/hazel",
  urls = ["https://github.com/tweag/rules_haskell/archive/master.tar.gz"],
)

load("@ai_formation_hazel//:packages.bzl","core_packages","packages")
load("@ai_formation_hazel//:hazel.bzl","hazel_repositories")
hazel_repositories(core_packages=core_packages,packages=packages)
'''
