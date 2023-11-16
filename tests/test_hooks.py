#!/usr/bin/env python3

from contextlib import contextmanager
from typing import Generator, Any

import bsst

from test_util import CaptureStdout

testcase = """
$a // bsst-plugin(test_hooks): dplh
42 // bsst-plugin(test_hooks): pushdata
SUB // bsst-plugin(test_hooks): sub
DUP
IF
SIZE
ELSE
VERIFY // bsst-plugin(test_hooks): fail
ENDIF
SWAP DROP
"""


@contextmanager
def FreshEnv() -> Generator[bsst.SymEnvironment, None, None]:
    env = bsst.SymEnvironment()
    env.use_parallel_solving = False
    env.log_progress = False
    env.solver_timeout_seconds = 0
    env.z3_enabled = True
    env.produce_model_values = False

    with bsst.CurrentEnvironment(env):
        bp = bsst.Branchpoint(pc=0, branch_index=0)
        with bsst.CurrentExecContext(bp.context):
            yield env


g_state_copy: dict[str, Any] = {}


def plugin_settings(env: bsst.SymEnvironment, value_str: str,
                    state: dict[str, Any]) -> None:
    state['setting'] = int(value_str)
    g_state_copy.update(state.copy())


def plugin_comment(env: bsst.SymEnvironment, comment_text: str,
                   op_pos: int, line_no: int, state: dict[str, Any]) -> None:
    if comment_text == 'dplh':
        assert op_pos == 0
        assert line_no == 2
        state['dplh_at'] = op_pos
    elif comment_text == 'pushdata':
        assert op_pos == 1
        assert line_no == 3
        state['pushdata_at'] = op_pos
    elif comment_text == 'sub':
        assert op_pos == 2
        assert line_no == 4
        state['sub_at'] = op_pos
    elif comment_text == 'fail':
        state['fail_at'] = op_pos
    else:
        assert 0, "unexpected comment"

    g_state_copy.update(state.copy())


def pushdata(env: bsst.SymEnvironment, ctx: bsst.ExecContext,
             sd: bsst.ScriptData, phf: bsst.PluginStackHelperFunctions,
             state: dict[str, Any]) -> None:

    if ctx.pc == state['dplh_at']:
        assert sd.name == '$a'
    elif ctx.pc == state['pushdata_at']:
        assert sd.value == 42
        assert phf.stacktop(-1).as_scriptnum_int() == 42
        phf.popstack()
        phf.push(bsst.SymData(static_value=99))
        state['pushdata_done'] = True

    g_state_copy.update(state.copy())


def pre_opcode(env: bsst.SymEnvironment, ctx: bsst.ExecContext,
               op: bsst.OpCode, phf: bsst.PluginStackHelperFunctions,
               state: dict[str, Any]) -> bool:
    if op == bsst.OP_SUB:
        assert ctx.pc == state['sub_at']
        assert phf.stacktop(-1).as_scriptnum_int() == 99
        phf.popstack()
        phf.push(bsst.SymData(static_value=555))
        state['pre_opcode_done'] = True

    g_state_copy.update(state.copy())

    return False


def post_opcode(env: bsst.SymEnvironment, ctx: bsst.ExecContext,
                op: bsst.OpCode, phf: bsst.PluginStackHelperFunctions,
                state: dict[str, Any]) -> None:
    if op == bsst.OP_SUB:
        assert ctx.pc == state['sub_at']
        assert str(phf.stacktop(-1)) == 'SUB($a, 555)'
        v = phf.stacktop(-1)
        phf.popstack()
        phf.push(bsst.SymData(name='TEST', args=(v,)))
        state['post_opcode_done'] = True

    g_state_copy.update(state.copy())


def pre_finalize(env: bsst.SymEnvironment, ctx: bsst.ExecContext,
                 state: dict[str, Any]) -> None:
    assert str(ctx.stack[-1]) == 'SIZE(TEST(SUB($a, 555)))'
    assert not ctx.is_finalized
    state['pre_finalize_done'] = True

    g_state_copy.update(state.copy())


def post_finalize(env: bsst.SymEnvironment, ctx: bsst.ExecContext,
                  state: dict[str, Any]) -> None:
    assert ctx.is_finalized
    state['post_finalize_done'] = True

    g_state_copy.update(state.copy())


def script_failure(env: bsst.SymEnvironment, ctx: bsst.ExecContext,
                   state: dict[str, Any]) -> None:

    assert ctx.failure
    pc, err = ctx.failure
    assert pc == state['fail_at']
    state['failure_detected'] = True
    g_state_copy.update(state.copy())


def report_start(env: bsst.SymEnvironment, state: dict[str, Any]) -> None:
    env.write_line('TEST_HOOKS_REPORT_START')


def report_end(env: bsst.SymEnvironment, state: dict[str, Any]) -> None:
    env.write_line('TEST_HOOKS_REPORT_END')


def parse_input_file(env: bsst.SymEnvironment, state: dict[str, Any]
                     ) -> 'bsst.ScriptInfo':
    state['parse_input_file'] = env.input_file
    return bsst.parse_script_lines(testcase.split('\n'))


def test() -> None:
    with FreshEnv() as env:
        with bsst.PluginContext('test_hooks'):
            env.set_hooks(parse_input_file=parse_input_file,
                          plugin_settings=plugin_settings,
                          plugin_comment=plugin_comment,
                          script_failure=script_failure,
                          report_start=report_start,
                          report_end=report_end,
                          pushdata=pushdata,
                          pre_opcode=pre_opcode,
                          post_opcode=post_opcode,
                          pre_finalize=pre_finalize,
                          post_finalize=post_finalize)

        bsst.parse_cmdline_args(['--input-file=test123',
                                 '--plugin-test-hooks=111'])

        out: str = ''
        with CaptureStdout() as output:
            bsst.main()
            out = output.getvalue()

        assert out.startswith('TEST_HOOKS_REPORT_START\n')
        assert out.endswith('TEST_HOOKS_REPORT_END\n')

        assert g_state_copy['parse_input_file'] == 'test123'
        assert g_state_copy['setting'] == 111

        assert 'dplh_at' in g_state_copy
        assert 'pushdata_at' in g_state_copy
        assert 'sub_at' in g_state_copy
        assert 'fail_at' in g_state_copy

        assert g_state_copy['pushdata_done']
        assert g_state_copy['pre_opcode_done']
        assert g_state_copy['post_opcode_done']
        assert g_state_copy['pre_finalize_done']
        assert g_state_copy['post_finalize_done']
        assert g_state_copy['failure_detected']


if __name__ == '__main__':
    test()
