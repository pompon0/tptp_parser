
def _hs_stack_binaries(ctx):
  proto_files = [f for dep in ctx.attr.protos for f in dep[ProtoInfo].direct_sources]
  for f in ctx.outputs.bins:
  out_dir = ctx.outputs.bins[0].dirname
  
  ctx.actions.run(
    inputs = ctx.files.srcs + proto_files,
    outputs = ctx.outputs.bins,
    executable = "stack",
    arguments = ["install", "--local-bin-path={}".format(out_dir)],
    use_default_shell_env = True, # requires original HOME and PATH variables (see .bazelrc)
  )

hs_stack_binaries = rule(
  implementation = _hs_stack_binaries,
  attrs = {
    "srcs": attr.label_list(allow_files = True, mandatory = True),
    "protos": attr.label_list(providers = [[ProtoInfo]]),
    "bins": attr.output_list(mandatory = True),
  },
  toolchains = ["@bazel_tools//tools/cpp:toolchain_type"],
)
