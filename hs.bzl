
def _hs_stack_binaries(ctx):
  proto_files = [f for dep in ctx.attr.protos for f in dep[ProtoInfo].direct_sources]
  out_dir = ctx.outputs.bins[0].dirname
  root_dir = ctx.files.stack_yaml[0].dirname
  print(root_dir)
  ctx.actions.run_shell(
    inputs = ctx.files.srcs + proto_files + ctx.files.stack_yaml,
    outputs = ctx.outputs.bins,
    command = "cat /proc/mounts && export OUT=`realpath {}` && export HOME=~ && export PATH=$PATH && cd {} && stack install --local-bin-path=$OUT".format(out_dir,root_dir),
    # use_default_shell_env = True, # requires original HOME and PATH variables (see .bazelrc)
  )

hs_stack_binaries = rule(
  implementation = _hs_stack_binaries,
  attrs = {
    "stack_yaml": attr.label(allow_single_file = True, mandatory = True),
    "srcs": attr.label_list(allow_files = True, mandatory = True),
    "protos": attr.label_list(providers = [[ProtoInfo]]),
    "bins": attr.output_list(mandatory = True),
  },
  toolchains = ["@bazel_tools//tools/cpp:toolchain_type"],
)
