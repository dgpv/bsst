# Plugins for B'SST

Plugins are python modules that B'SST can load at startup.

The set of plugins to load is given via `--plugins` setting, which is a comma-separated set of paths to plugin files.

Plugin file name must end with `_bsst_plugin.py`, otherwise B'SST will refuse to load it.

For example, with `--plugins=plugins/op_example_bsst_plugin.py`, B'SST will recognize `EXAMPLE` custom opcode.

There is no stable API for plugins as of now. To write plugins for B'SST your need a good understanding of the internals of `bsst` module. Still, the system of plugins is implemented for those who are ready to deal with studying `bsst` internals and with possible breaking changes in new versions of B'SST

On startup, each loaded plugin will get its `init()` function called, with two
arguments:

- First is the `bsst` module object (of type `ModuleType`). It is a module from which the plugin is called. It is advised to use that module instead of directly importing `bsst` from the plugin. You can look how it is done in the plugins in this directory (just assign to global `bsst` variable in `init()`, and optionally do mock-import to satisfy mypy typechecker). Note that you can access the `VERSION` attribute of the supplied module to check the running B'SST version

- Second is the "analysis environment" (of type `bsst.SymEnvironment`). It gives access to various convenience methods, but most important method for the plugin is `set_hooks()`.

NOTE: if you create new opcodes with `bsst.OpCode`, please do it inside the plugin's `init()` function or inside hook functions, otherwise it won't work.

To instument the behavior of B'SST, use `set_hooks()` method of the
`SymEnvironment` instance supplied to the init function.

It takes handler functions as keyword arguments:

* `parse_input_file`: called to parse the input file
* `plugin_settings`: called for `--bsst-plugin-<name>=` command line setting
* `plugin_comment`: called for `// bsst-plugin(<name>):` comment
* `script_failure`: called when script failure is detected
* `report_start`: called just before report is generated
* `report_end`: called just after report is printed
* `pushdata`: called just after data is put on the stack
* `pre_opcode`: called just before the opcode is to be executed (can be used to add custom opcodes)
* `post_opcode`: called just after opcode was executed
* `pre_finalize`: called just before execution context is finalized (last opcode was executed)
* `post_finalize`: called just after execution context was finalized (result on the stack was checked, `OP_DEPTH` results was adjusted, etc.)

For details on how to use these hooks, please look into `test_hooks.py` in the 'tests' directory of B'SST repository, and also into plugins in this directory

Plugins in this directory:

* `op_example_bsst_plugin.py`: A simple example of how to add custom opcode
* `raw_input_bsst_plugin.py`: Allows to supply hex or binary input to B'SST instead of text script source. Will use `python-bitcointx` and `python-elementstx` python packages to decode the input, therefore python packages must be available. Recognizes settings `--plugin-raw-input=hex` (the default) and `--plugin-raw-input=binary`. Will output the decoded script, each line will have a comment displaying the offset of the opcode/data in this line
* `checksig_track_bsst_plugin.py`: Analyses arguments and results of `CHECKSIG(VERIFY)`, `CHECKMULTISIG(VERIFY)` and `CHECKSIGADD` opcodes to determine if particular execution path can be successful without at least one successful signature check. If such situation is possible, will add `warn_possible_success_without_sig_check` to the list of warnings for particular execution path
* `model_value_usage_track_plugin.py`: Gives additional information about the usage of the values for which 'model values' are generated, such as if they there used as a signature or a preimage, or in which enforcement they are involved
