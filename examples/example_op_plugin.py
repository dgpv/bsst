from typing import Union
from types import ModuleType

if not Union:  # always false
    # Fool mypy to think we have imported bsst.
    # It will be instead supplied to us via init function.
    import bsst
else:
    bsst: ModuleType  # type: ignore


class CustomOpCodes:
    OP_EXAMPLE: 'bsst.OpCode'


ops = CustomOpCodes()


def init(_bsst: ModuleType) -> None:
    global bsst
    bsst = _bsst  # set bsst to the module supplied from the main program

    ops.OP_EXAMPLE = bsst.OpCode(0xFF, 'EXAMPLE')


def exec_opcode(
    ctx: 'bsst.ExecContext',
    env: 'bsst.SymEnvironment',
    op: 'bsst.OpCode',
    phf: 'bsst.PluginHelperFunctions'
) -> bool:
    if op == ops.OP_EXAMPLE:
        val = phf.stacktop(-1)
        r = bsst.SymData(name=op.name, args=(val,))

        r.set_as_Int(val.use_as_Int() + 42)

        phf.popstack()
        phf.push(r)

        return True  # opcode was processed

    return False  # we did not recognize the opcode
