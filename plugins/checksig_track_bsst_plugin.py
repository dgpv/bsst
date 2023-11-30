from types import ModuleType
from typing import Any, Union

if not Any:
    # we only need z3 for typechecking, mock-import it
    import z3
    # mock-import bsst - for mypy. we will set bsst global inside init()
    import bsst


def pre_finalize(env: 'bsst.SymEnvironment', ctx: 'bsst.ExecContext',
                 state: dict[str, Any]) -> None:

    checksig_results: list[Union[int, 'z3.ExprRef']] = []

    if not env.z3_enabled:
        ctx.add_warning('Checksig tracking is not performed because '
                        'Z3 is not enabled')
        return

    for pc, op, r in ctx.sig_check_operations:
        if op in (bsst.OP_CHECKSIGVERIFY, bsst.OP_CHECKMULTISIGVERIFY):
            checksig_results.append(1)
        elif op in (bsst.OP_CHECKSIG, bsst.OP_CHECKMULTISIG):
            checksig_results.append(r.as_Int())
        elif op == bsst.OP_CHECKSIGADD:
            checksig_results.append(r.as_Int() - r.args[1].as_Int())
        elif op in (bsst.OP_CHECKSIGFROMSTACK,
                    bsst.OP_CHECKSIGFROMSTACKVERIFY):
            pass
        else:
            ctx.add_warning(
                f'opcode {op} at {bsst.op_pos_info(pc)} performs signature '
                f'check, but is not supported by {bsst.cur_plugin_name()}'
                f'plugin')

    accum: Union[int, 'z3.ExprRef'] = 0
    for res in checksig_results:
        accum += res

    ww = bsst.SymData(name='warn_possible_success_without_sig_check')
    bsst.Check(ww.as_Int() == bsst.If(accum == 0, 1, 0))
    ctx.z3_warning_vars.append((ctx.pc, ww))


# returns a 'state' for the plugin, which will be passed to the hooks
def init(bsst_module: ModuleType, env: 'bsst.SymEnvironment'
         ) -> dict[str, Any]:

    global bsst
    bsst = bsst_module

    env.set_hooks(pre_finalize=pre_finalize)

    return {}
