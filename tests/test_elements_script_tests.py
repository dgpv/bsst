#!/usr/bin/env python3

import re
import os
import sys
import json
import random
from contextlib import contextmanager
from typing import Generator, NoReturn

import elementstx  # noqa
from bitcointx import select_chain_params
from bitcointx.core.script import CScript

import bsst

# pylama:ignore=E501,C901

is_tapscript = False

SKIP_UNTIL_TESTCASE = 0


@contextmanager
def FreshEnv(*, z3_enabled: bool = False
             ) -> Generator[bsst.SymEnvironment, None, None]:
    env = bsst.SymEnvironment()
    if is_tapscript:
        env.sigversion = bsst.SigVersion.TAPSCRIPT
    else:
        env.sigversion = bsst.SigVersion.BASE

    env.is_elements = True
    env.z3_enabled = z3_enabled
    env.use_parallel_solving = False
    env.solver_timeout_seconds = 0

    with bsst.CurrentEnvironment(env):
        bsst.try_import_optional_modules()
        with bsst.CurrentExecContext(env.get_root_branch().context):
            yield env


def maybe_subst_with_nop(op_str: str, flags: list[str]) -> str:
    # We do not support some opcodes, but we still want to run
    # testcases that contain them, so we just substitute with NOP.
    # CLTV and CSV have to be replaced if flags do not enable them,
    # because we don't simulate script flags for them
    if op_str in ('VER', 'RESERVED') or \
            re.match('(NOP|RESERVED)\\d+', op_str) or \
            (op_str in ('CHECKLOCKTIMEVERIFY', 'CHECKSEQUENCEVERIFY')
             and op_str not in flags):
        return 'NOP'

    return op_str


def convert_script(line: str, flags: list[str],
                   ) -> tuple[bsst.OpCode | bsst.ScriptData, ...] | None:
    script_bytes: list[bytes] = []
    for op_str in line.split():
        if not op_str:
            continue

        if is_tapscript and op_str.lower().startswith("le64("):
            assert op_str.endswith(')')
            op_str = op_str[5:-1]

            sign = 1
            if op_str.startswith('-'):
                sign = -1
                op_str = op_str[1:]

            if not op_str.isdigit():
                die('incorrect argument to le64()')

            if op_str.startswith('0') and len(op_str) > 1:
                die('no leading zeroes allowed')

            v = int(op_str)*sign
            script_bytes.append(b'\x08'+bytes(bsst.IntLE64.from_int(v)))

        elif op_str.lower().startswith("0x"):
            data_str = op_str[2:]
            script_bytes.append(bytes.fromhex(data_str))
        elif (op_str.isdigit() or (op_str.startswith('-')
                                   and op_str[1:].isdigit())):
            sign = 1
            if op_str.startswith('-'):
                sign = -1
                op_str = op_str[1:]

            if op_str.startswith('0') and len(op_str) > 1:
                die('no leading zeroes allowed')

            script_bytes.append(CScript([int(op_str)*sign]))
        elif len(op_str) >= 2 and op_str[0] == "'" and op_str[-1] == "'":
            script_bytes.append(CScript([op_str[1:-1].encode('utf-8')]))
        else:
            ops = bsst.get_opcodes([maybe_subst_with_nop(op_str, flags)]).body
            assert len(ops) == 1
            assert isinstance(ops[0], bsst.OpCode)
            script_bytes.append(CScript(bytes([ops[0].code])))

    if not script_bytes:
        return None

    script_lines: list[str] = []
    for sop, data, _ in CScript(b''.join(script_bytes)).raw_iter():
        if data is not None:
            script_lines.append(f'x(\'{data.hex()}\')')
        else:
            op_str = repr(sop)
            if re.match('CScriptOp\\(0x..\\)', op_str):
                for op in bsst.cur_env().get_enabled_opcodes():
                    if op.code == int(sop):
                        op_str = op.name
                        break
                else:
                    return None
            else:
                assert op_str.startswith('OP_'), op_str
                op_str = op_str[3:]

            if op_str in ('SMALLINTEGER', 'PUBKEYS', 'PUBKEYHASH', 'PUBKEY',
                          'INVALIDOPCODE'):
                return None

            script_lines.append(maybe_subst_with_nop(op_str, flags))

    return bsst.get_opcodes(script_lines).body


supported_flags = {'DISCOURAGE_UPGRADEABLE_PUBKEY_TYPE', 'STRICTENC',
                   'WITNESS_PUBKEYTYPE', 'MINIMALIF', 'MINIMALDATA', 'LOW_S',
                   'NULLFAIL', 'CLEANSTACK', 'NULLDUMMY'}


def common_env_settings(env: bsst.SymEnvironment, flags: list[str]) -> None:
    env.discourage_upgradeable_pubkey_type_flag = \
        'DISCOURAGE_UPGRADEABLE_PUBKEY_TYPE' in flags
    env.strictenc_flag = 'STRICTENC' in flags
    env.witness_pubkeytype_flag = 'WITNESS_PUBKEYTYPE' in flags
    env.minimalif_flag = 'MINIMALIF' in flags
    env.minimaldata_flag = 'MINIMALDATA' in flags
    env.minimaldata_flag_strict = 'MINIMALDATA' in flags
    env.low_s_flag = 'LOW_S' in flags
    env.nullfail_flag = 'NULLFAIL' in flags
    env.cleanstack_flag = 'CLEANSTACK' in flags
    env.nulldummy_flag = 'NULLDUMMY' in flags


valid_contexts: list[bsst.ExecContext] = []
invalid_contexts: list[bsst.ExecContext] = []
failures: list[str] = []


def clean_contexts() -> None:
    valid_contexts.clear()
    invalid_contexts.clear()
    failures.clear()


def process_contexts(env: bsst.SymEnvironment) -> None:
    def do_processing(bp: 'bsst.Branchpoint', level: int) -> None:
        if bp.context is not None:
            if bp.context.failure:
                invalid_contexts.append(bp.context)
                err = bp.context.failure[1]
                if err.startswith(bsst.SCRIPT_FAILURE_PREFIX_SOLVER):
                    for fc in bsst.parse_failcodes(err):
                        failures.append(fc[0])
                else:
                    failures.append(err)
            else:
                valid_contexts.append(bp.context)

    clean_contexts()
    root_bp = env.get_root_branch()
    root_bp.walk_branches(do_processing)


def set_script_body(script_body: tuple[bsst.OpCode | bsst.ScriptData, ...]
                    ) -> None:
    line_no_table = []
    for pc in range(len(script_body)):
        line_no_table.append(pc)

    line_no_table.append(len(script_body))

    env = bsst.cur_env()
    env.script_info = bsst.ScriptInfo(body=script_body,
                                      line_no_table=line_no_table)


def process_testcase_single(
    *,
    scriptPubKey: tuple[bsst.OpCode | bsst.ScriptData, ...],
    witness_data: list[bsst.ScriptData],
    flags: list[str],
    comment: str,
    expected_result: str,
    z3_enabled: bool,
    use_nonstatic_witnesses: bool = False,
    flags_were_altered: bool = False
) -> None:
    if use_nonstatic_witnesses:
        assert z3_enabled

    def check_p2sh() -> None:
        assert len(scriptPubKey) == 3
        assert scriptPubKey[0] == bsst.OP_HASH160
        assert isinstance(scriptPubKey[1], bsst.ScriptData)
        assert isinstance(scriptPubKey[1].value, bytes)
        assert len(scriptPubKey[1].value) == 0x14
        assert scriptPubKey[2] == bsst.OP_EQUAL

    with FreshEnv(z3_enabled=z3_enabled) as env:
        set_script_body(scriptPubKey)
        common_env_settings(env, flags)
        env.z3_enabled = z3_enabled
        env.do_progressive_z3_checks = True
        env.log_progress = True
        env.log_solving_attempts = True

        root_bp = env.get_root_branch()

        for i, wd in enumerate(witness_data):
            if env.minimaldata_flag_strict and wd.is_non_minimal:
                if not flags_were_altered:
                    assert expected_result in ('MINIMALDATA', 'UNKNOWN_ERROR')
                return

            static_data_name = f'<witness_data_static_{i}>'
            static_data = bsst.SymData(static_value=wd.value,
                                       name=static_data_name,
                                       unique_name=static_data_name)
            if use_nonstatic_witnesses:
                data_name = f'<witness_data_{i}>'
                data = bsst.SymData(name=data_name, unique_name=data_name)
                bsst.Check(data.use_as_ByteSeq() == static_data.as_ByteSeq())
            else:
                data = static_data

            assert root_bp.context
            root_bp.context.stack.append(data)
            data.increase_refcount()

        try:
            bsst.symex_script()
        except ValueError as e:
            if str(e).startswith('non-static value:'):
                if expected_result == 'INVALID_STACK_OPERATION':
                    return

                if use_nonstatic_witnesses:
                    if expected_result == 'OK' and \
                            str(e).endswith(' non-static argument'):
                        return

                    if expected_result in ('OK', 'SIG_COUNT') and \
                            re.search(' cannot use it for number of keys ', str(e)):
                        return

                    if expected_result == 'UNKNOWN_ERROR' and \
                            str(e).endswith(' non-static argument'):
                        return

            raise

        process_contexts(env)

        bsst.report()
        sys.stdout.flush()

        if expected_result == 'OK':
            if comment.startswith('2-of-2 CHECKMULTISIG NOT with '
                                  'the second pubkey invalid'):
                if 'STRICTENC' in flags:
                    assert len(valid_contexts) == 0, (
                        'This testcase cannot be correctly sym-executed, '
                        'because we cannot check if the signature is correct '
                        'because we do not simulate transaction hash'
                    )
                return

            if comment == 'P2SH with CLEANSTACK':
                check_p2sh()
                return

            if comment in ('Overly long signature is correctly encoded',
                           'Missing S is correctly encoded',
                           'S with invalid S length is correctly encoded',
                           'Non-integer S is correctly encoded',
                           'Non-integer R is correctly encoded',
                           'Zero-length R is correctly encoded',
                           'Zero-length S is correctly encoded for DERSIG',
                           'Negative S is correctly encoded'):
                assert len(valid_contexts) == 0, (
                    'This testcase cannot be correctly sym-executed, '
                    'because we assume DERSIG flag is always true'
                )
                return

            if 'DERSIG' not in flags and \
                    (comment.endswith('but no DERSIG') or
                        comment.endswith('without DERSIG')):
                return

            if comment.startswith(">201 opcodes, but RESERVED (0x50) doesn't count"):
                assert len(valid_contexts) == 0, (
                    'We replase RESERVED with NOPs, thus this testcase will fail'
                )
                return

            if use_nonstatic_witnesses:
                if comment == 'BIP66 example 12, with DERSIG':
                    return

            assert len(valid_contexts) == 1, 'exactly one valid context is expected'
            assert len(valid_contexts[0].used_witnesses) == 0, \
                'script is not expected to access stack positions that are not defined'
            return

        if expected_result in ('DISCOURAGE_UPGRADABLE_NOPS'):
            return

        if expected_result.startswith('WITNESS_'):
            return

        if 'P2SH' in flags and 'WITNESS' in flags and \
                scriptPubKey[0] == bsst.OP_HASH160:
            return

        if len(valid_contexts) > 0:
            for ctx in valid_contexts:
                if expected_result in ('EVAL_FALSE', 'EQUALVERIFY') and \
                        comment.startswith('P2SH'):
                    check_p2sh()
                elif expected_result == 'EVAL_FALSE':
                    if ctx.used_witnesses:
                        assert ctx.stack[-1] is ctx.used_witnesses[0]
                    elif comment == 'P2PK, bad sig':
                        pass
                elif expected_result == 'UNBALANCED_CONDITIONAL':
                    assert (
                        env.script_info.body[ctx.used_witnesses[0].src_pc]
                        in (bsst.OP_IF, bsst.OP_NOTIF)
                    )
                elif (expected_result == 'UNSATISFIED_LOCKTIME' and
                        comment.endswith('tx version < 2')):
                    pass
                elif (use_nonstatic_witnesses and
                      expected_result == 'EQUALVERIFY' and
                      len(valid_contexts) == 1 and
                      valid_contexts[0].enforcements[0].cond.name == 'EQUALVERIFY' and
                      valid_contexts[0].enforcements[0].cond.args[0].name == 'HASH160' and
                      valid_contexts[0].enforcements[0].cond.args[0].args[0].name == '<witness_data_1>'):
                    pass
                elif (not z3_enabled and
                      expected_result == 'NULLFAIL' and
                      len(valid_contexts) == 1 and
                      valid_contexts[0].enforcements[0].cond.name == 'NOT' and
                      valid_contexts[0].enforcements[0].cond.args[0].name == 'CHECKSIG' and
                      valid_contexts[0].enforcements[0].cond.args[0].args[0].name == '<witness_data_static_0>'):
                    pass
                elif z3_enabled and expected_result == 'SIG_HIGH_S':
                    # LOW_S is only supported for static signature data
                    pass
                else:
                    assert expected_result == 'INVALID_STACK_OPERATION'
                    assert len(ctx.used_witnesses) > 0

            return

        assert len(valid_contexts) == 0

        if flags_were_altered:
            # with altered flags, we only care that the script has failed
            return

        if expected_result == 'UNBALANCED_CONDITIONAL':
            assert any(f.startswith('unbalanced conditional')
                       for f in failures)
        elif expected_result == 'OP_RETURN':
            assert any(f == 'OP_RETURN encountered' for f in failures)
        elif expected_result == 'VERIFY':
            assert any(f == 'check_verify' for f in failures)
        elif expected_result == 'EQUALVERIFY':
            assert any(f == 'check_equalverify' for f in failures)
        elif expected_result == 'INVALID_ALTSTACK_OPERATION':
            assert any(f == 'altstack underflow' for f in failures)
        elif expected_result == 'INVALID_STACK_OPERATION':
            assert (any(len(ctx.used_witnesses) > 0
                        for ctx in invalid_contexts)
                    or
                    (any(f in ('PICK: negative argument',
                               'ROLL: negative argument')
                         for f in failures))
                    or
                    (len(invalid_contexts) == 1 and
                     len(failures) == 1 and
                     ((failures[0] == 'check_length_mismatch' and
                       env.script_info.body[invalid_contexts[0].pc] in (bsst.OP_AND,
                                                                        bsst.OP_OR))
                      or
                      (failures[0] in ('check_negative_argument',
                                       'check_argument_above_bounds')
                       and
                       env.script_info.body[invalid_contexts[0].pc] in (bsst.OP_SUBSTR,))
                      or
                      (failures[0] == 'check_data_too_long' and
                       env.script_info.body[invalid_contexts[0].pc] in (bsst.OP_CAT,)))))
        elif expected_result == 'PUSH_SIZE':
            assert any(f == 'check_data_too_long' for f in failures)
        elif expected_result == 'OP_COUNT':
            assert any(f == 'Maximum opcode count is reached' for f in failures)
        elif expected_result == 'STACK_SIZE':
            assert any(f.startswith('stack overflow') for f in failures)
        elif expected_result == 'PUBKEY_COUNT':
            assert any(re.search('\\binvalid keys count\\b', f) for f in failures)
        elif expected_result == 'SIG_COUNT':
            assert any(re.search('\\binvalid signature count\\b', f) for f in failures)
        elif expected_result == 'MINIMALDATA':
            assert any(re.search('\\bnon-minimal immediate data encountered\\b', f) for f in failures)
        elif expected_result == 'PUBKEYTYPE':
            assert any(
                re.search('\\btrying to constrain value\\(s\\) with size\\(s\\) \\(33, 65\\) ', f)
                or
                f == 'check_invalid_pubkey'
                for f in failures)
        elif expected_result == 'SIG_HASHTYPE':
            assert any(f in ('check_signature_bad_hashtype',
                             'check_signature_explicit_sighash_all')
                       for f in failures)
        elif expected_result == 'SIG_DER':
            assert any(f in ('check_invalid_signature_length',
                             'check_invalid_signature_encoding')
                       for f in failures)
        elif expected_result == 'NULLFAIL':
            assert any(f == 'check_signature_nullfail' for f in failures)
        elif expected_result == 'SIG_HIGH_S':
            assert any(f == 'check_signature_low_s' for f in failures)
        elif expected_result == 'SIG_HASHTYPE':
            assert any(f == 'check_signature_bad_hashtype' for f in failures)
        elif expected_result == 'SIG_NULLDUMMY':
            assert any((f.endswith('extra byte is not zero') or
                        f == 'check_checkmultisig_bugbyte_zero')
                       for f in failures)
        elif expected_result == 'CLEANSTACK':
            assert any(f.startswith('Cleanstack rule fail') for f in failures)
        elif expected_result == 'NEGATIVE_LOCKTIME':
            assert any(f == 'check_negative_argument' for f in failures)
        elif expected_result == 'UNSATISFIED_LOCKTIME':
            # This test checks for 'tx_version < 2', but we do not set
            # tx_version, on the contrary, tx_version can be
            # constrained by the sym-execution of CHECKSEQUENCEVERIFY.
            # Therefore, we just ignore that this test fails with
            # different cause
            assert scriptPubKey == (bsst.OP_CHECKSEQUENCEVERIFY,)
            assert any(f in ('top of stack is always False after script end',
                             'check_final_verify') for f in failures)
        elif is_tapscript and expected_result == 'LE64_EXPECT8BYTES':
            assert any((f.startswith('expected 8 bytes') or
                        f == 'check_le64_wrong_size') for f in failures)
        elif is_tapscript and expected_result == 'LE64_BOUNDS':
            assert any(f in ('check_invalid_arguments', 'check_int64_out_of_bounds')
                       for f in failures)
        elif is_tapscript and expected_result == 'SCRIPTNUM_BOUNDS':
            assert any(f == 'check_scriptnum_out_of_bounds' for f in failures)
        elif is_tapscript and expected_result == 'INVALID_ARGUMENTS':
            assert 'check_invalid_arguments' in failures
        else:
            assert expected_result in ('EVAL_FALSE', 'UNKNOWN_ERROR')


def die(msg: str) -> NoReturn:
    sys.stderr.write(f'ERROR: {msg}\n')
    sys.exit(-1)


def process_testcase(
    *,
    scriptSig: tuple[bsst.OpCode | bsst.ScriptData, ...] | None,
    scriptPubKey: tuple[bsst.OpCode | bsst.ScriptData, ...],
    flags: list[str],
    comment: str,
    expected_result: str,
    flags_were_altered: bool = False,
    z3_only: bool = False
) -> None:

    print(f"Process with flags {flags}")

    clean_contexts()

    if scriptSig:
        with FreshEnv() as env:
            set_script_body(scriptSig)
            common_env_settings(env, flags)
            env.is_incomplete_script = True

            print("Sym-exec SSig")

            bsst.symex_script()
            bsst.report()
            sys.stdout.flush()

            process_contexts(env)

            if len(valid_contexts) == 0:
                if expected_result == 'UNKNOWN_ERROR':
                    return

                if expected_result == 'UNBALANCED_CONDITIONAL':
                    assert any(f.startswith('unbalanced conditional')
                               for f in failures)
                    return

            assert len(valid_contexts) > 0

            if any(len(c.used_witnesses) > 0 for c in valid_contexts):
                assert expected_result == 'INVALID_STACK_OPERATION'
                assert all(len(c.used_witnesses) > 0
                           for c in valid_contexts)
                return

    witness_data: list[bsst.ScriptData] = []

    if valid_contexts:
        assert len(valid_contexts) == 1
        ctx = valid_contexts[0]
        with bsst.CurrentExecContext(ctx):
            for sd in ctx.stack:
                mv = sd.get_model_value()
                if mv is None:
                    v = None
                else:
                    v = mv.single_value

                if v is None:
                    v = b'<arbitrary data>'
                elif isinstance(v, str):
                    v = v.encode('utf-8')
                elif isinstance(v, bsst.IntLE64):
                    v = bytes(v)

                witness_data.append(
                    bsst.ScriptData(name=None, value=v,
                                    do_check_non_minimal='MINIMALDATA' in flags))

    print("Sym-exec SPK")

    if not z3_only:
        print("NO Z3")
        process_testcase_single(
            scriptPubKey=scriptPubKey,
            witness_data=witness_data,
            comment=comment, flags=flags,
            expected_result=expected_result,
            z3_enabled=False, flags_were_altered=flags_were_altered)

    print("WITH Z3")
    process_testcase_single(
            scriptPubKey=scriptPubKey,
            witness_data=witness_data,
            comment=comment, flags=flags,
            expected_result=expected_result,
            z3_enabled=True, flags_were_altered=flags_were_altered)

    print("WITH Z3 and non-static witnesses")
    process_testcase_single(
            scriptPubKey=scriptPubKey,
            witness_data=witness_data,
            comment=comment, flags=flags,
            expected_result=expected_result,
            z3_enabled=True, use_nonstatic_witnesses=True,
            flags_were_altered=flags_were_altered)


def test() -> None:
    global is_tapscript

    if len(sys.argv) < 2:
        die('must specify path to script_tests.json and chain name\n')

    select_chain_params('elements')

    if len(sys.argv) == 3 and sys.argv[2] == 'tapscript':
        is_tapscript = True

    with open(sys.argv[1], 'r') as f:
        tc_no = 0
        for testcase in json.load(f):
            if len(testcase) < 2:
                # a comment, skip it.
                continue

            tc_no += 1
            print("TESTCASE no.", tc_no)
            if tc_no < SKIP_UNTIL_TESTCASE:
                continue

            if isinstance(testcase[0], list):
                # skip witness program tests
                continue

            print("TESTCASE body:", testcase)

            flags = testcase[2].split(',')
            expected_result = testcase[3]
            if expected_result in ('BAD_OPCODE', 'DISABLED_OPCODE'):
                continue

            with FreshEnv():
                scriptSig = convert_script(testcase[0], flags)
                scriptPubKey = convert_script(testcase[1], flags)

            if scriptPubKey is None:
                continue

            comment = ''
            if len(testcase) > 4:
                comment = testcase[4]

            print("SSig", scriptSig)
            print("SPK", scriptPubKey)
            print("FLAGS", flags)
            print("ERes", expected_result)
            print()

            if expected_result in ('SCRIPT_SIZE', 'SIG_PUSHONLY'):
                # we do not model these
                continue

            if expected_result == 'MINIMALDATA':
                if re.match('PUSHDATA\\d+ of \\d+ bytes minimally represented',
                            comment):
                    continue

            z3_only = False
            if 'Z3' in flags:
                z3_only = True
                flags.remove('Z3')

            process_testcase(
                scriptSig=scriptSig, scriptPubKey=scriptPubKey,
                flags=flags, comment=comment, expected_result=expected_result,
                z3_only=z3_only)

            if os.getenv('BSST_TESTS_NO_FLAGS_SHUFFLE'):
                continue

            if expected_result == 'OK':
                random.shuffle(flags)
                # check that removing flags does not change the result
                while(flags):
                    flags.pop()
                    process_testcase(
                        scriptSig=scriptSig, scriptPubKey=scriptPubKey,
                        flags=flags, comment=comment,
                        expected_result=expected_result,
                        flags_were_altered=True, z3_only=z3_only)
            else:
                # check that adding flags does not change the result
                flags_to_add = list(supported_flags - set(flags))
                random.shuffle(flags_to_add)
                while(flags_to_add):
                    process_testcase(
                        scriptSig=scriptSig, scriptPubKey=scriptPubKey,
                        flags=flags+list(flags_to_add), comment=comment,
                        expected_result=expected_result,
                        flags_were_altered=True, z3_only=z3_only)
                    flags_to_add.pop()


if __name__ == '__main__':
    test()
