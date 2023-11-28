from types import ModuleType
from typing import Any, Union

if not Any:
    # we only need z3 for typechecking, mock-import it
    import z3
    # mock-import bsst - for mypy. we will set bsst global inside init()
    import bsst


def pre_opcode(
    env: 'bsst.SymEnvironment',
    ctx: 'bsst.ExecContext',
    op: 'bsst.OpCode',
    phf: 'bsst.PluginStackHelperFunctions',
    _state: dict[str, Any]
) -> bool:
    if op == bsst.OP_CHECKSIGADD:
        if len(ctx.stack) < 2:
            return False

        plugin_data = ctx.get_plugin_data()
        plugin_data['checksigadd_prev_n'] = ctx.stack[-2]

    return False


def post_opcode(
    env: 'bsst.SymEnvironment',
    ctx: 'bsst.ExecContext',
    op: 'bsst.OpCode',
    phf: 'bsst.PluginStackHelperFunctions',
    state: dict[str, Any]
) -> None:
    plugin_data = ctx.get_plugin_data()

    _old_accum: bsst.SymData | None = None

    def old_accum_integer() -> Union[int, 'z3.ArithRef']:
        if _old_accum:
            return _old_accum.as_Int()
        else:
            return 0

    if 'accum' not in state:
        counter = 0
    else:
        _old_accum, counter = plugin_data['accum']
        assert isinstance(_old_accum, bsst.SymData)
        assert isinstance(counter, int)

    def get_new_accum() -> bsst.SymData:
        nonlocal counter
        new_accum = bsst.SymData(
            unique_name=f'checksig_track_{id(ctx)}_{counter}')
        new_accum.use_as_Int()
        counter += 1
        return new_accum

    checks: list['z3.ExprRef']

    if 'checks' not in plugin_data:
        plugin_data['checks'] = []

    checks = plugin_data['checks']

    if op in (bsst.OP_CHECKSIGVERIFY, bsst.OP_CHECKMULTISIGVERIFY):
        new_accum = get_new_accum()
        checks.append(new_accum.as_Int() == old_accum_integer() + 1)
    elif op in (bsst.OP_CHECKSIG, bsst.OP_CHECKMULTISIG):
        new_accum = get_new_accum()
        checks.append(
            new_accum.as_Int() == old_accum_integer() + ctx.stack[-1].as_Int())
    elif op == bsst.OP_CHECKSIGADD:
        prev_n = plugin_data['checksigadd_prev_n']
        new_accum = get_new_accum()
        checks.append(
            new_accum.as_Int() ==
            old_accum_integer() +
            (ctx.stack[-1].as_Int() - prev_n.as_Int()))
    else:
        return

    plugin_data['accum'] = (new_accum, counter)


def pre_finalize(env: 'bsst.SymEnvironment', ctx: 'bsst.ExecContext',
                 state: dict[str, Any]) -> None:
    plugin_data = ctx.get_plugin_data()

    if 'accum' not in plugin_data:
        return

    accum, _ = plugin_data['accum']
    assert isinstance(accum, bsst.SymData)

    for check in plugin_data['checks']:
        bsst.Check(check)

    ww = bsst.SymData(name='warn_possible_success_without_sig_check')
    bsst.Check(ww.as_Int() == bsst.If(accum.as_Int() == 0, 1, 0))
    ctx.z3_warning_vars.append((ctx.pc, ww))


# returns a 'state' for the plugin, which will be passed to the hooks
def init(bsst_module: ModuleType, env: 'bsst.SymEnvironment'
         ) -> dict[str, Any]:

    global bsst
    bsst = bsst_module

    env.set_hooks(pre_opcode=pre_opcode,
                  post_opcode=post_opcode,
                  pre_finalize=pre_finalize)

    return {}
