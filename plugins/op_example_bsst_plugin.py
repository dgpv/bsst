from typing import Any
from types import ModuleType

if not Any:  # always false
    # mock-import bsst - for mypy. we will set bsst global inside init()
    import bsst


class CustomOpCodes:
    OP_EXAMPLE: 'bsst.OpCode'


ops = CustomOpCodes()


def handle_opcode(
    env: 'bsst.SymEnvironment',
    ctx: 'bsst.ExecContext',
    op: 'bsst.OpCode',
    phf: 'bsst.PluginStackHelperFunctions',
    state: dict[str, Any]
) -> bool:
    if op == ops.OP_EXAMPLE:
        val = phf.stacktop(-1)
        r = bsst.SymData(name=op.name, args=(val,))

        r.set_as_Int(val.use_as_Int() + 42)

        phf.popstack()
        phf.push(r)

        return True  # opcode was processed by the plugin

    return False  # continue normal processing


# returns a 'state' for the plugin, which will be passed to the hooks
def init(bsst_module: ModuleType, env: 'bsst.SymEnvironment'
         ) -> dict[str, Any]:

    global bsst
    bsst = bsst_module

    env.set_hooks(pre_opcode=handle_opcode)

    ops.OP_EXAMPLE = bsst.OpCode(0xFF, 'EXAMPLE')

    return {}
