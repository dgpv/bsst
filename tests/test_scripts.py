#!/usr/bin/env python3

import os
import struct
from contextlib import contextmanager
from typing import Generator, Iterable

from bitcointx.core.key import CKey, XOnlyPubKey

import bsst

from test_util import CaptureStdout

# pylama:ignore=E501


@contextmanager
def FreshEnv(*, z3_enabled: bool = False, is_tapscript: bool = False,
             is_witness_v0: bool = False,
             assume_no_160bit_hash_collisions: bool = False,
             nullfail_flag: bool = True,
             ) -> Generator[bsst.SymEnvironment, None, None]:
    env = bsst.SymEnvironment()
    env.is_elements = True
    env.z3_enabled = z3_enabled
    env.produce_model_values = False
    env.use_parallel_solving = False
    env.assume_no_160bit_hash_collisions = assume_no_160bit_hash_collisions
    env.nullfail_flag = nullfail_flag
    if is_tapscript:
        assert not is_witness_v0
        env.sigversion = bsst.SigVersion.TAPSCRIPT
    elif is_witness_v0:
        assert not is_tapscript
        env.sigversion = bsst.SigVersion.WITNESS_V0
    else:
        env.sigversion = bsst.SigVersion.BASE

    with bsst.CurrentEnvironment(env):
        with bsst.CurrentExecContext(env.get_root_branch().context):
            yield env


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


def do_test_single(script: str, *,
                   z3_enabled: bool = False,
                   is_tapscript: bool = False,
                   is_witness_v0: bool = False,
                   assume_no_160bit_hash_collisions: bool = False,
                   expect_failures: Iterable[str] = (),
                   num_successes: int = 1,
                   nullfail_flag: bool = True,
                   ) -> list[str]:
    print(f'script: {script}')
    print(f'z3_enabled: {z3_enabled}')
    print()

    with FreshEnv(z3_enabled=z3_enabled,
                  is_tapscript=is_tapscript, is_witness_v0=is_witness_v0,
                  assume_no_160bit_hash_collisions=assume_no_160bit_hash_collisions,
                  nullfail_flag=nullfail_flag
                  ) as env:

        env.script_info = bsst.parse_script_lines(script.split('\n'))

        bsst.symex_script()
        bsst.report()

        process_contexts(env)

        assert len(valid_contexts) == num_successes, len(valid_contexts)
        if not expect_failures:
            assert len(invalid_contexts) == 0
        else:
            assert len(invalid_contexts) > 0
            assert not (set(failures) - set(expect_failures)), failures

        return failures


def do_test(script: str, *,
            expect_failures: Iterable[str] = (),
            num_successes: int = 1,
            is_tapscript: bool = False,
            nullfail_flag: bool = False) -> None:
    do_test_single(script, z3_enabled=False,
                   is_tapscript=is_tapscript, expect_failures=expect_failures,
                   num_successes=num_successes,
                   nullfail_flag=nullfail_flag)
    do_test_single(script, z3_enabled=True,
                   is_tapscript=is_tapscript, expect_failures=expect_failures,
                   num_successes=num_successes,
                   nullfail_flag=nullfail_flag)


def test() -> None:
    out: str = ''

    k = CKey.from_secret_bytes(os.urandom(32))
    xpub = XOnlyPubKey(k.pub)
    data = os.urandom(32)
    sig_ecdsa = k.sign(data)
    sig_schnorr = k.sign_schnorr_no_tweak(data)

    do_test(f"0x{sig_ecdsa.hex()}01 DUP TOALTSTACK 0x{k.pub.hex()} CHECKSIGVERIFY FROMALTSTACK 0x{k.pub.hex()} CHECKSIG")
    do_test(f"DUP 0x{sig_ecdsa.hex()}01 EQUALVERIFY DUP TOALTSTACK 0x{k.pub.hex()} CHECKSIGVERIFY FROMALTSTACK 0x{k.pub.hex()} CHECKSIG")
    do_test(f"DUP 0x{sig_ecdsa.hex()} EQUALVERIFY DUP TOALTSTACK 0x01 CAT 0x{k.pub.hex()} CHECKSIG NOT VERIFY FROMALTSTACK 0x02 CAT 0x{k.pub.hex()} CHECKSIG",
            nullfail_flag=False)
    do_test(f"DUP 0x{sig_schnorr.hex()} EQUALVERIFY DUP TOALTSTACK 0x01 0x{xpub.hex()} CHECKSIGFROMSTACK NOT VERIFY FROMALTSTACK 0x02 0x{xpub.hex()} CHECKSIGFROMSTACK",
            nullfail_flag=False, is_tapscript=True)
    failures = do_test_single(f"DUP 0x{sig_schnorr.hex()}01 EQUALVERIFY DUP TOALTSTACK 0x{xpub.hex()} CHECKSIGVERIFY FROMALTSTACK 0x{xpub.hex()} CHECKSIG",
                              is_tapscript=True, z3_enabled=False,
                              expect_failures=['check_signature_explicit_sighash_all', 'check_equalverify', 'check_known_args_different_result', 'check_known_result_different_args'],
                              num_successes=0)
    assert 'check_signature_explicit_sighash_all' in failures
    failures = do_test_single(f"DUP 0x{sig_schnorr.hex()}01 EQUALVERIFY DUP TOALTSTACK 0x{xpub.hex()} CHECKSIGVERIFY FROMALTSTACK 0x{xpub.hex()} CHECKSIG",
                              is_tapscript=True, z3_enabled=True,
                              expect_failures=['check_signature_explicit_sighash_all', 'check_equalverify', 'check_known_args_different_result', 'check_known_result_different_args', 'check_checksigverify'],
                              num_successes=0)
    assert 'check_signature_explicit_sighash_all' in failures

    failures = do_test_single(f"0x{sig_ecdsa.hex()}01 DUP TOALTSTACK 0x{k.pub.hex()} CHECKSIGVERIFY FROMALTSTACK 0x{k.pub.hex()} CHECKSIG NOT VERIFY",
                              expect_failures=['check_known_args_different_result', 'check_checksigverify', 'check_verify'],
                              num_successes=0,
                              z3_enabled=True, nullfail_flag=False)
    assert 'check_known_args_different_result' in failures

    failures = do_test_single(f"DUP 0x{sig_ecdsa.hex()}01 EQUALVERIFY DUP TOALTSTACK 0x{k.pub.hex()} CHECKSIGVERIFY FROMALTSTACK 0x{k.pub.hex()} CHECKSIG NOT VERIFY",
                              expect_failures=['check_known_args_different_result', 'check_checksigverify', 'check_verify'],
                              num_successes=0,
                              z3_enabled=True, nullfail_flag=False)
    assert 'check_known_args_different_result' in failures

    failures = do_test_single(f"0x{sig_ecdsa.hex()}02 0x{k.pub.hex()} CHECKSIGVERIFY 0x{sig_ecdsa.hex()}01 0x{k.pub.hex()} CHECKSIG",
                              expect_failures=['check_known_result_different_args', 'check_known_args_different_result', 'check_checksigverify', 'check_final_verify'],
                              num_successes=0,
                              z3_enabled=True, nullfail_flag=False)
    assert 'check_known_result_different_args' in failures

    failures = do_test_single(f"DUP 0x{sig_ecdsa.hex()}02 EQUALVERIFY 0x{k.pub.hex()} CHECKSIGVERIFY 0x{sig_ecdsa.hex()}01 0x{k.pub.hex()} CHECKSIG",
                              expect_failures=['check_known_result_different_args', 'check_known_args_different_result', 'check_checksigverify', 'check_final_verify', 'check_equalverify',
                                               'check_invalid_signature_encoding', 'check_invalid_signature_length', 'check_signature_low_s', 'check_signature_bad_hashtype'],
                              num_successes=0,
                              z3_enabled=True, nullfail_flag=False)
    assert 'check_known_result_different_args' in failures

    failures = do_test_single(f"0x{sig_schnorr.hex()} DUP TOALTSTACK 0x01 0x{xpub.hex()} CHECKSIGFROMSTACKVERIFY FROMALTSTACK 0x01 0x{xpub.hex()} CHECKSIGFROMSTACK NOT",
                              expect_failures=['check_known_result_different_args', 'check_known_args_different_result', 'check_checksigfromstackverify', 'check_final_verify'],
                              num_successes=0, is_tapscript=True,
                              z3_enabled=True, nullfail_flag=False)
    assert 'check_known_args_different_result' in failures

    failures = do_test_single(f"0x{sig_schnorr.hex()} DUP TOALTSTACK 0x01 0x{xpub.hex()} CHECKSIGFROMSTACKVERIFY FROMALTSTACK 0x02 0x{xpub.hex()} CHECKSIGFROMSTACK",
                              expect_failures=['check_known_result_different_args', 'check_known_args_different_result', 'check_checksigfromstackverify', 'check_final_verify'],
                              num_successes=0, is_tapscript=True,
                              z3_enabled=True, nullfail_flag=False)
    assert 'check_known_result_different_args' in failures

    failures = do_test_single(f"2DUP TOALTSTACK TOALTSTACK 0x02 CAT SWAP 0 SWAP CHECKSIGADD FROMALTSTACK DUP 0x{xpub.hex()} EQUALVERIFY FROMALTSTACK DUP 0x{sig_schnorr.hex()} EQUALVERIFY 0x03 CAT ROT ROT CHECKSIGADD 1 EQUAL",
                              expect_failures=['check_known_result_different_args', 'check_known_args_different_result', 'check_signature_bad_hashtype', 'check_invalid_signature_length', 'check_equalverify', 'check_final_verify'],
                              num_successes=0, is_tapscript=True,
                              z3_enabled=True, nullfail_flag=False)
    assert 'check_known_result_different_args' in failures

    do_test("TXWEIGHT 4000000 EQUAL", is_tapscript=True)
    failures = do_test_single("TXWEIGHT 4000001 EQUAL",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_final_verify'])

    failures = do_test_single("DUP INSPECTNUMINPUTS 2 EQUALVERIFY INSPECTINPUTSEQUENCE DROP 3 EQUAL",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_argument_above_bounds', 'check_equalverify', 'check_final_verify', 'check_negative_argument'])
    assert 'check_argument_above_bounds' in failures

    failures = do_test_single("DUP INSPECTNUMOUTPUTS 2 EQUALVERIFY INSPECTOUTPUTNONCE DROP 3 EQUAL",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_argument_above_bounds', 'check_equalverify', 'check_final_verify', 'check_negative_argument'])
    assert 'check_argument_above_bounds' in failures

    lktime_threshold_hex = struct.pack('<i', bsst.LOCKTIME_THRESHOLD).hex()
    do_test_single(f"INSPECTLOCKTIME 0x{lktime_threshold_hex} EQUALVERIFY {bsst.LOCKTIME_THRESHOLD} CHECKLOCKTIMEVERIFY",
                   is_tapscript=True, z3_enabled=True, num_successes=1)
    failures = do_test_single(f"INSPECTLOCKTIME 0x{lktime_threshold_hex} EQUALVERIFY 1 CHECKLOCKTIMEVERIFY",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_locktime_type_mismatch', 'check_equalverify'])
    assert 'check_locktime_type_mismatch' in failures

    failures = do_test_single(f"INSPECTLOCKTIME 0x00000000 EQUALVERIFY {bsst.LOCKTIME_THRESHOLD} CHECKLOCKTIMEVERIFY",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_locktime_type_mismatch', 'check_equalverify', 'check_locktime_timelock_in_effect', 'check_negative_argument'])
    assert 'check_locktime_type_mismatch' in failures

    failures = do_test_single("INSPECTLOCKTIME 0x00000000 EQUALVERIFY 10 CHECKLOCKTIMEVERIFY",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_locktime_type_mismatch', 'check_equalverify', 'check_locktime_timelock_in_effect'])
    assert 'check_locktime_timelock_in_effect' in failures

    failures = do_test_single("PUSHCURRENTINPUTINDEX INSPECTINPUTSEQUENCE 0xffffffff EQUALVERIFY CHECKLOCKTIMEVERIFY",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_cltv_nsequence_final', 'check_equalverify'])
    assert 'check_cltv_nsequence_final' in failures

    failures = do_test_single("PUSHCURRENTINPUTINDEX DUP INSPECTVERSION 0x02000000 EQUALVERIFY INSPECTINPUTSEQUENCE 0xffffffff EQUALVERIFY CHECKSEQUENCEVERIFY 111 EQUAL",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_nsequence_type_mismatch', 'check_equalverify', 'check_final_verify', 'check_nsequence_timelock_in_effect'])
    assert 'check_nsequence_type_mismatch' in failures

    failures = do_test_single("PUSHCURRENTINPUTINDEX DUP INSPECTVERSION 0x01000000 EQUALVERIFY INSPECTINPUTSEQUENCE 0xffffffff EQUALVERIFY CHECKSEQUENCEVERIFY 111 EQUAL",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_nsequence_type_mismatch', 'check_equalverify', 'check_final_verify', 'check_bad_tx_version'])
    assert 'check_bad_tx_version' in failures

    failures = do_test_single("PUSHCURRENTINPUTINDEX DUP INSPECTVERSION 0x02000000 EQUALVERIFY INSPECTINPUTSEQUENCE 0x000000ff EQUALVERIFY CHECKSEQUENCEVERIFY 1111 EQUAL",
                              is_tapscript=True, z3_enabled=True, num_successes=0,
                              expect_failures=['check_nsequence_timelock_in_effect', 'check_nsequence_type_mismatch', 'check_equalverify', 'check_final_verify', 'check_scriptnum_minimal_encoding'])
    assert 'check_nsequence_timelock_in_effect' in failures

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTOUTPUTASSET TOALTSTACK TOALTSTACK 1 INSPECTOUTPUTASSET SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1)
        out = output.getvalue()

    assert "<*> EQUAL(OUTPUT_1_ASSET, OUTPUT_ASSET(wit0))" in out
    assert "<*> EQUAL(OUTPUT_1_ASSET_PREFIX, OUTPUT_ASSET_PREFIX(wit0))" in out

    do_test_single("DUP INSPECTOUTPUTASSET TOALTSTACK TOALTSTACK 1 INSPECTOUTPUTASSET SWAP FROMALTSTACK EQUAL NOT VERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])
    do_test_single("DUP INSPECTOUTPUTASSET TOALTSTACK TOALTSTACK 1 INSPECTOUTPUTASSET SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUAL NOT VERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTOUTPUTVALUE TOALTSTACK TOALTSTACK 1 INSPECTOUTPUTVALUE SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1)
        out = output.getvalue()

    assert "<*> EQUAL(OUTPUT_1_VALUE, OUTPUT_VALUE(wit0))" in out
    assert "<*> EQUAL(OUTPUT_1_VALUE_PREFIX, OUTPUT_VALUE_PREFIX(wit0))" in out

    do_test_single("DUP INSPECTOUTPUTVALUE TOALTSTACK TOALTSTACK 1 INSPECTOUTPUTVALUE SWAP FROMALTSTACK EQUAL NOT VERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])
    do_test_single("DUP INSPECTOUTPUTVALUE TOALTSTACK TOALTSTACK 1 INSPECTOUTPUTVALUE SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUAL NOT VERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTOUTPUTSCRIPTPUBKEY TOALTSTACK TOALTSTACK 1 INSPECTOUTPUTSCRIPTPUBKEY SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1)
        out = output.getvalue()

    assert "<*> EQUAL(OUTPUT_1_SPK_WITPROG, OUTPUT_SPK_WITPROG(wit0))" in out
    assert "<*> EQUAL(OUTPUT_1_SPK_WITVER, OUTPUT_SPK_WITVER(wit0))" in out

    do_test_single("DUP INSPECTOUTPUTSCRIPTPUBKEY TOALTSTACK TOALTSTACK 1 INSPECTOUTPUTSCRIPTPUBKEY SWAP FROMALTSTACK EQUAL NOT VERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])
    do_test_single("DUP INSPECTOUTPUTSCRIPTPUBKEY TOALTSTACK TOALTSTACK 1 INSPECTOUTPUTSCRIPTPUBKEY SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUAL NOT VERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTOUTPUTNONCE TOALTSTACK 1 INSPECTOUTPUTNONCE FROMALTSTACK EQUALVERIFY 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1)
        out = output.getvalue()

    assert "<*> EQUAL(OUTPUT_1_NONCE, OUTPUT_NONCE(wit0))" in out

    do_test_single("DUP INSPECTOUTPUTNONCE TOALTSTACK 1 INSPECTOUTPUTNONCE FROMALTSTACK EQUAL NOT VERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTINPUTOUTPOINT TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTOUTPOINT ROT FROMALTSTACK EQUALVERIFY SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1)
        out = output.getvalue()

    assert "<*> EQUAL(INPUT_1_OUTPOINT_HASH, INPUT_OUTPOINT_HASH(wit0))" in out
    assert "<*> EQUAL(INPUT_1_OUTPOINT_PREVOUT_N, INPUT_OUTPOINT_PREVOUT_N(wit0))" in out
    assert "<*> EQUAL(INPUT_1_OUTPOINT_FLAG, INPUT_OUTPOINT_FLAG(wit0))" in out

    do_test_single("DUP INSPECTINPUTOUTPOINT TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTOUTPOINT ROT FROMALTSTACK EQUAL NOT VERIFY SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0,
                   expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])
    do_test_single("DUP INSPECTINPUTOUTPOINT TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTOUTPOINT ROT FROMALTSTACK EQUALVERIFY SWAP FROMALTSTACK EQUAL NOT VERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])
    do_test_single("DUP INSPECTINPUTOUTPOINT TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTOUTPOINT ROT FROMALTSTACK EQUALVERIFY SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUAL NOT VERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTINPUTASSET TOALTSTACK TOALTSTACK 1 INSPECTINPUTASSET SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1)
        out = output.getvalue()

    assert "<*> EQUAL(INPUT_1_ASSET, INPUT_ASSET(wit0))" in out
    assert "<*> EQUAL(INPUT_1_ASSET_PREFIX, INPUT_ASSET_PREFIX(wit0))" in out

    do_test_single("DUP INSPECTINPUTASSET TOALTSTACK TOALTSTACK 1 INSPECTINPUTASSET SWAP FROMALTSTACK EQUAL NOT VERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])
    do_test_single("DUP INSPECTINPUTASSET TOALTSTACK TOALTSTACK 1 INSPECTINPUTASSET SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUAL NOT VERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTINPUTVALUE TOALTSTACK TOALTSTACK 1 INSPECTINPUTVALUE SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1)
        out = output.getvalue()

    assert "<*> EQUAL(INPUT_1_VALUE, INPUT_VALUE(wit0))" in out
    assert "<*> EQUAL(INPUT_1_VALUE_PREFIX, INPUT_VALUE_PREFIX(wit0))" in out

    do_test_single("DUP INSPECTINPUTVALUE TOALTSTACK TOALTSTACK 1 INSPECTINPUTVALUE SWAP FROMALTSTACK EQUAL NOT VERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])
    do_test_single("DUP INSPECTINPUTVALUE TOALTSTACK TOALTSTACK 1 INSPECTINPUTVALUE SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUAL NOT VERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify', 'check_scriptnum_minimal_encoding'])

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTINPUTSCRIPTPUBKEY TOALTSTACK TOALTSTACK 1 INSPECTINPUTSCRIPTPUBKEY SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1)
        out = output.getvalue()

    assert "<*> EQUAL(INPUT_1_SPK_WITPROG, INPUT_SPK_WITPROG(wit0))" in out
    assert "<*> EQUAL(INPUT_1_SPK_WITVER, INPUT_SPK_WITVER(wit0))" in out

    do_test_single("DUP INSPECTINPUTSCRIPTPUBKEY TOALTSTACK TOALTSTACK 1 INSPECTINPUTSCRIPTPUBKEY SWAP FROMALTSTACK EQUAL NOT VERIFY FROMALTSTACK EQUALVERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])
    do_test_single("DUP INSPECTINPUTSCRIPTPUBKEY TOALTSTACK TOALTSTACK 1 INSPECTINPUTSCRIPTPUBKEY SWAP FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUAL NOT VERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTINPUTSEQUENCE TOALTSTACK 1 INSPECTINPUTSEQUENCE FROMALTSTACK EQUALVERIFY 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1)
        out = output.getvalue()

    assert "<*> EQUAL(INPUT_1_SEQUENCE, INPUT_SEQUENCE(wit0))" in out

    do_test_single("DUP INSPECTINPUTSEQUENCE TOALTSTACK 1 INSPECTINPUTSEQUENCE FROMALTSTACK EQUAL NOT VERIFY 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_equalverify', 'check_verify'])

    with CaptureStdout() as output:
        do_test_single("DUP INSPECTINPUTISSUANCE SIZE VERIFY TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTISSUANCE SIZE VERIFY 5 PICK FROMALTSTACK EQUALVERIFY 4 PICK FROMALTSTACK EQUALVERIFY 3 PICK FROMALTSTACK EQUALVERIFY 2 PICK FROMALTSTACK EQUALVERIFY 1 PICK FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY DROP DROP DROP DROP DROP 1 EQUAL",
                       is_tapscript=True, z3_enabled=True, num_successes=1, expect_failures=['check_verify'])
        out = output.getvalue()

    assert "<*> BOOL(SIZE(INPUT_ISSUANCE_ASSETBLINDINGNONCE(wit0)))" in out
    assert "<*> BOOL(SIZE(INPUT_1_ISSUANCE_ASSETBLINDINGNONCE))" in out
    assert "<*> EQUAL(INPUT_1_ISSUANCE_INFLATIONKEYS, INPUT_ISSUANCE_INFLATIONKEYS(wit0))" in out
    assert "<*> EQUAL(INPUT_1_ISSUANCE_INFLATIONKEYS_PREFIX, INPUT_ISSUANCE_INFLATIONKEYS_PREFIX(wit0))" in out
    assert "<*> EQUAL(INPUT_1_ISSUANCE_AMOUNT, INPUT_ISSUANCE_AMOUNT(wit0))" in out
    assert "<*> EQUAL(INPUT_1_ISSUANCE_AMOUNT_PREFIX, INPUT_ISSUANCE_AMOUNT_PREFIX(wit0))" in out
    assert "<*> EQUAL(INPUT_1_ISSUANCE_ASSETENTROPY, INPUT_ISSUANCE_ASSETENTROPY(wit0))" in out
    assert "<*> EQUAL(INPUT_1_ISSUANCE_ASSETBLINDINGNONCE, INPUT_ISSUANCE_ASSETBLINDINGNONCE(wit0))" in out

    do_test_single("DUP INSPECTINPUTISSUANCE SIZE VERIFY TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTISSUANCE SIZE VERIFY 5 PICK FROMALTSTACK EQUAL NOT VERIFY 4 PICK FROMALTSTACK EQUALVERIFY 3 PICK FROMALTSTACK EQUALVERIFY 2 PICK FROMALTSTACK EQUALVERIFY 1 PICK FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY DROP DROP DROP DROP DROP 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_verify', 'check_equalverify'])
    do_test_single("DUP INSPECTINPUTISSUANCE SIZE VERIFY TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTISSUANCE SIZE VERIFY 5 PICK FROMALTSTACK EQUALVERIFY 4 PICK FROMALTSTACK EQUAL NOT VERIFY 3 PICK FROMALTSTACK EQUALVERIFY 2 PICK FROMALTSTACK EQUALVERIFY 1 PICK FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY DROP DROP DROP DROP DROP 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_verify', 'check_equalverify'])
    do_test_single("DUP INSPECTINPUTISSUANCE SIZE VERIFY TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTISSUANCE SIZE VERIFY 5 PICK FROMALTSTACK EQUALVERIFY 4 PICK FROMALTSTACK EQUALVERIFY 3 PICK FROMALTSTACK EQUAL NOT VERIFY 2 PICK FROMALTSTACK EQUALVERIFY 1 PICK FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY DROP DROP DROP DROP DROP 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_verify', 'check_equalverify'])
    do_test_single("DUP INSPECTINPUTISSUANCE SIZE VERIFY TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTISSUANCE SIZE VERIFY 5 PICK FROMALTSTACK EQUALVERIFY 4 PICK FROMALTSTACK EQUALVERIFY 3 PICK FROMALTSTACK EQUALVERIFY 2 PICK FROMALTSTACK EQUAL NOT VERIFY 1 PICK FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUALVERIFY DROP DROP DROP DROP DROP 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_verify', 'check_equalverify'])
    do_test_single("DUP INSPECTINPUTISSUANCE SIZE VERIFY TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTISSUANCE SIZE VERIFY 5 PICK FROMALTSTACK EQUALVERIFY 4 PICK FROMALTSTACK EQUALVERIFY 3 PICK FROMALTSTACK EQUALVERIFY 2 PICK FROMALTSTACK EQUALVERIFY 1 PICK FROMALTSTACK EQUAL NOT VERIFY FROMALTSTACK EQUALVERIFY DROP DROP DROP DROP DROP 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_verify', 'check_equalverify', 'check_scriptnum_minimal_encoding'])
    do_test_single("DUP INSPECTINPUTISSUANCE SIZE VERIFY TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK TOALTSTACK 1 INSPECTINPUTISSUANCE SIZE VERIFY 5 PICK FROMALTSTACK EQUALVERIFY 4 PICK FROMALTSTACK EQUALVERIFY 3 PICK FROMALTSTACK EQUALVERIFY 2 PICK FROMALTSTACK EQUALVERIFY 1 PICK FROMALTSTACK EQUALVERIFY FROMALTSTACK EQUAL NOT VERIFY DROP DROP DROP DROP DROP 1 EQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify', 'check_verify', 'check_equalverify'])

    # explicit value 1 is ok for input
    do_test("inspectinputvalue 1 equalverify le64(1) equal",
            is_tapscript=True)
    # explicit value 0 is not possible - no spendable 0-value outputs are
    # allowed
    do_test_single("inspectinputvalue 1 equalverify le64(0) equal",
                   is_tapscript=True, z3_enabled=True, expect_failures=['check_equalverify', 'check_final_verify'], num_successes=0)

    failures = do_test_single("0x304502203e4516da7253cf068effec6b95c41221c0cf3a8e6ccb8cbf1725b562e9afde2c022100ab1e3da73d67e32045a20e0b999e049978ea8d6ee5480d485fcf2ce0d03b2ef001 0x03d8bd1a69a1337d2817cfc0fecc3247436b34903d7ae424316354b73114dcb1dd CHECKSIG",
                              z3_enabled=False, num_successes=0, expect_failures=['check_signature_low_s', 'check_invalid_signature_length', 'check_invalid_signature_encoding'])
    assert 'check_signature_low_s' in failures
    failures = do_test_single("0x304402203e4516da7253cf068effec6b95c41221c0cf3a8e6ccb8cbf1725b562e9afde2c02207FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A101 0x03d8bd1a69a1337d2817cfc0fecc3247436b34903d7ae424316354b73114dcb1dd CHECKSIG",
                              z3_enabled=False, num_successes=0, expect_failures=['check_signature_low_s', 'check_invalid_signature_length', 'check_invalid_signature_encoding'])
    assert 'check_signature_low_s' in failures

    do_test_single("DUP 0 BOOLOR SWAP 0 EQUALVERIFY",
                   z3_enabled=False, num_successes=1)
    do_test_single("DUP 0 BOOLOR SWAP 0 EQUALVERIFY",
                   z3_enabled=True, num_successes=0, expect_failures=['check_equalverify', 'check_final_verify'])

    # 0-value output unspendable because of OP_RETURN
    do_test("DUP INSPECTOUTPUTVALUE 1 EQUALVERIFY le64(0) EQUALVERIFY INSPECTOUTPUTSCRIPTPUBKEY SWAP x('6a') SHA256 EQUALVERIFY -1 NUMEQUAL",
            is_tapscript=True)
    # 0-value output, but not unspendable (detectable only with z3)
    do_test_single("DUP INSPECTOUTPUTVALUE 1 EQUALVERIFY le64(0) EQUALVERIFY INSPECTOUTPUTSCRIPTPUBKEY SWAP x('6b') SHA256 EQUALVERIFY -1 NUMEQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_equalverify'])
    # 0-value output, but witver is 0
    do_test_single("DUP INSPECTOUTPUTVALUE 1 EQUALVERIFY le64(0) EQUALVERIFY INSPECTOUTPUTSCRIPTPUBKEY SWAP x('6a') SHA256 EQUALVERIFY 0 NUMEQUAL",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_final_verify'])

    out = ''
    with CaptureStdout() as output:
        do_test_single("IF 2DUP EQUALVERIFY 1 EQUALVERIFY 1 EQUALVERIFY ELSE EQUALVERIFY ENDIF",
                       z3_enabled=True, num_successes=2)
        out = output.getvalue()

    print(out)
    assert ("When BOOL(wit0) :: [IF @ 0:L1]\n------------------------------\n\n        <*> EQUAL(wit1, wit2) @ 2:L1\n        <*> EQUAL(1, wit1) @ 4:L1\n        <*> EQUAL(1, wit2) @ 6:L1\n\n"
            in out)

    out = ''
    with CaptureStdout() as output:
        do_test_single("IF 2DUP 1 EQUALVERIFY 1 EQUALVERIFY ENDIF EQUALVERIFY",
                       z3_enabled=True, num_successes=2)
        out = output.getvalue()

    print(out)
    assert ("When BOOL(wit0) :: [IF @ 0:L1]\n------------------------------\n\n        <*> EQUAL(1, wit1) @ 3:L1\n        <*> EQUAL(1, wit2) @ 5:L1\n        {*} EQUAL(wit1, wit2) @ 7:L1\n\n"
            in out)

    do_test_single("le64(1) x('1000000000000080') MUL64 DROP",
                   z3_enabled=True, is_tapscript=True, num_successes=1, expect_failures=['check_branch_condition_invalid'])

    # check int64 overflow
    do_test_single("le64(1) x('FFFFFFFFFFFFFF7F') ADD64 VERIFY",
                   z3_enabled=False, is_tapscript=True, num_successes=0, expect_failures=['check_invalid_arguments'])
    do_test_single("le64(1) x('0000000000000080') SUB64 VERIFY",
                   z3_enabled=False, is_tapscript=True, num_successes=0, expect_failures=['check_invalid_arguments'])
    do_test_single("le64(2) x('0000000000000080') MUL64 VERIFY",
                   z3_enabled=False, is_tapscript=True, num_successes=0, expect_failures=['check_invalid_arguments'])
    do_test_single("x('FFFFFFF000000000') DUP MUL64 VERIFY",
                   z3_enabled=False, is_tapscript=True, num_successes=0, expect_failures=['check_invalid_arguments'])
    do_test_single("x('FFFFFFFFFFFFFF7F') DUP ADD64 VERIFY",
                   z3_enabled=False, is_tapscript=True, num_successes=0, expect_failures=['check_invalid_arguments'])
    do_test_single("x('0000000000000080') DUP ADD64 VERIFY",
                   z3_enabled=False, is_tapscript=True, num_successes=0, expect_failures=['check_invalid_arguments'])
    do_test_single("le64(0) x('0000000000000080') SUB64 VERIFY",
                   z3_enabled=False, is_tapscript=True, num_successes=0, expect_failures=['check_invalid_arguments'])

    do_test_single("DUP SCRIPTNUMTOLE64 x('FFFFFFFFFFFFFF7F') ADD64 VERIFY SWAP 1 NUMEQUALVERIFY",
                   z3_enabled=True, is_tapscript=True, num_successes=0, expect_failures=['check_int64_out_of_bounds', 'check_numequalverify', 'check_verify'])
    do_test_single("DUP SCRIPTNUMTOLE64 x('0000000000000080') SUB64 VERIFY SWAP 1 NUMEQUALVERIFY",
                   z3_enabled=True, is_tapscript=True, num_successes=0, expect_failures=['check_int64_out_of_bounds', 'check_numequalverify', 'check_verify'])
    do_test_single("DUP SCRIPTNUMTOLE64 x('0000000000000080') MUL64 VERIFY SWAP 2 NUMEQUALVERIFY",
                   z3_enabled=True, is_tapscript=True, num_successes=0, expect_failures=['check_int64_out_of_bounds', 'check_numequalverify', 'check_verify'])
    do_test_single("DUP DUP MUL64 VERIFY SWAP x('FFFFFFF000000000') EQUALVERIFY",
                   z3_enabled=True, is_tapscript=True, num_successes=0, expect_failures=['check_int64_out_of_bounds', 'check_equalverify', 'check_verify'])
    do_test_single("DUP DUP ADD64 VERIFY SWAP x('FFFFFFFFFFFFFF7F') EQUALVERIFY",
                   z3_enabled=True, is_tapscript=True, num_successes=0, expect_failures=['check_int64_out_of_bounds', 'check_equalverify', 'check_verify'])
    do_test_single("DUP DUP ADD64 VERIFY SWAP x('0000000000000080') EQUALVERIFY",
                   z3_enabled=True, is_tapscript=True, num_successes=0, expect_failures=['check_int64_out_of_bounds', 'check_equalverify', 'check_verify'])
    do_test_single("DUP x('0000000000000080') SUB64 VERIFY SWAP 0 SCRIPTNUMTOLE64 EQUALVERIFY",
                   z3_enabled=True, is_tapscript=True, num_successes=0, expect_failures=['check_int64_out_of_bounds', 'check_equalverify', 'check_verify'])

    # Invalid arguments, result will be out of bounds
    do_test("x('FFFFFFFFFFFFFF7F') 1 SCRIPTNUMTOLE64 ADD64 VERIFY",
            is_tapscript=True, num_successes=0, expect_failures=['check_invalid_arguments'])
    do_test_single("DUP INSPECTOUTPUTNONCE 1 INSPECTOUTPUTNONCE EQUAL SWAP 1 EQUALVERIFY NOT",
                   is_tapscript=True, z3_enabled=True, num_successes=0, expect_failures=['check_equalverify', 'check_final_verify'])
    do_test_single("DUP x('00') SWAP CAT SWAP x('0080') EQUALVERIFY DUP IF DUP ENDIF x('000080') XOR 0 RSHIFT NOT",
                   z3_enabled=True, num_successes=1, expect_failures=['check_branch_condition_invalid', 'check_equalverify', 'check_data_too_long'])
    do_test("SIZE 32 NUMEQUALVERIFY SWAP SIZE 50 NUMEQUALVERIFY x('3033021a') SWAP CAT SWAP x('02') SWAP CAT CHECKSIG")
    do_test('1 DEPTH DEPTH 3 EQUALVERIFY 2 EQUALVERIFY ADD')
    do_test('SIZE 0 EQUALVERIFY DUP CAT DUP CAT DUP CAT DUP CAT DUP CAT DUP CAT DUP CAT DUP CAT DUP CAT SIZE 0 NUMEQUALVERIFY NOT')
    do_test("DUP 2 RIGHT 'B' SWAP CAT SWAP 'ABCD' EQUALVERIFY 'BCD' EQUAL")
    do_test("DUP 2 3 SUBSTR 'F' CAT SWAP 2 RIGHT 'CDE' EQUALVERIFY 'CD' 'EF' CAT EQUAL")
    do_test("DUP 6 RSHIFT SWAP 134 EQUALVERIFY 2 NUMEQUAL")
    do_test("DUP 6 RSHIFT SWAP 4104 EQUALVERIFY x('40') EQUAL")
    do_test("DUP 6 RSHIFT SWAP 4104 NUMEQUALVERIFY 64 NUMEQUAL")
    do_test("DUP 0 RSHIFT SWAP x('0000') EQUALVERIFY 0 EQUAL")
    do_test("DUP 0 RSHIFT SWAP x('0100') EQUALVERIFY 1 EQUAL")
    do_test("DUP 8 RSHIFT SWAP x('0100') EQUALVERIFY 0 EQUAL")
    do_test("DUP 16 RSHIFT SWAP x('000010') EQUALVERIFY 16 EQUAL")
    do_test("DUP 32 RSHIFT SWAP x('00000000120000') EQUALVERIFY 18 EQUAL")
    do_test("DUP 30 RSHIFT SWAP x('00000000120000') EQUALVERIFY 72 EQUAL")
    do_test("DUP 17 RSHIFT SWAP x('000010') EQUALVERIFY 8 EQUAL")
    do_test("DUP 11 RSHIFT SWAP x('0010') EQUALVERIFY 2 EQUAL")
    do_test("0x99 12 LSHIFT x('009009') EQUAL")
    do_test("DUP 12 LSHIFT SWAP 0x99 EQUALVERIFY x('009009') EQUAL")
    do_test("DUP 6 LSHIFT SWAP 34 EQUALVERIFY 2176 EQUAL")
    do_test("DUP 18 LSHIFT SWAP x('860000') EQUALVERIFY 35127296 NUMEQUAL")
    do_test("DUP 9 LSHIFT SWAP x('8680') EQUALVERIFY 16845824 NUMEQUAL")
    do_test("DUP 8 LSHIFT SWAP x('8600') EQUALVERIFY -1536 NUMEQUAL")
    do_test("DUP 8 LSHIFT SWAP x('86') EQUALVERIFY -1536 NUMEQUAL")
    do_test("DUP 8 LSHIFT SWAP 2 EQUALVERIFY 512 NUMEQUAL")
    do_test("DUP 11 LSHIFT SWAP x('008000') EQUALVERIFY 67108864 EQUAL")
    do_test("DUP 0 LSHIFT SWAP x('0000') EQUALVERIFY 0 EQUAL")
    do_test("DUP 0 LSHIFT SWAP x('0100') EQUALVERIFY 1 EQUAL")
    do_test("DUP INVERT SWAP 85 EQUALVERIFY x('aa') EQUAL")
    do_test("DUP INVERT SWAP 84 NUMEQUALVERIFY x('ab') NUMEQUAL")
    do_test("DUP INVERT SWAP x('aaaa00') EQUALVERIFY x('5555ff') EQUAL")
    do_test("DUP x('99') XOR SWAP x('23') EQUALVERIFY x('ba') EQUAL")
    do_test("DUP x('5511FF99') XOR SWAP x('22758399') EQUALVERIFY 8152183 NUMEQUAL")
    do_test("DUP x('5511FF99') XOR SWAP x('22758390') EQUALVERIFY x('77647c09') EQUAL")
    do_test("DUP x('5511FF99') XOR SWAP x('5511FF99') EQUALVERIFY x('00000000') EQUAL")
    do_test("DUP x('5511FF99') AND SWAP x('22758399') EQUALVERIFY x('00118399') EQUAL")
    do_test("DUP x('99') AND SWAP x('23') EQUALVERIFY 1 EQUAL")
    do_test("DUP x('99') OR SWAP x('23') EQUALVERIFY x('bb') EQUAL")
    do_test("DUP x('5511FF99') OR SWAP x('22758399') EQUALVERIFY x('7775ff99') EQUAL")

    # equal hashes means equal data for strong hases
    do_test("2DUP HASH256 SWAP HASH256 EQUALVERIFY EQUAL")
    do_test("2DUP EQUALVERIFY HASH256 SWAP HASH256 EQUAL")
    do_test("2DUP SHA256 SWAP SHA256 EQUALVERIFY EQUAL")
    do_test("2DUP EQUALVERIFY SHA256 SWAP SHA256 EQUAL")
    # non-equal hashes means equal data for strong hases
    do_test("2DUP HASH256 SWAP HASH256 EQUAL NOT VERIFY EQUAL NOT")
    do_test("2DUP EQUAL NOT VERIFY HASH256 SWAP HASH256 EQUAL NOT")
    do_test("2DUP SHA256 SWAP SHA256 EQUAL NOT VERIFY EQUAL NOT")
    do_test("2DUP EQUAL NOT VERIFY SHA256 SWAP SHA256 EQUAL NOT")

    # non-equal hashes means non-equal data (only detectable with Z3)
    do_test_single("2DUP HASH256 SWAP HASH256 EQUALVERIFY EQUAL NOT",
                   z3_enabled=True, num_successes=0, expect_failures=['check_equalverify', 'check_final_verify'])
    do_test_single("2DUP EQUALVERIFY HASH256 SWAP HASH256 EQUAL NOT",
                   z3_enabled=True, num_successes=0, expect_failures=['check_equalverify', 'check_final_verify'])
    do_test_single("2DUP SHA256 SWAP SHA256 EQUALVERIFY EQUAL NOT",
                   z3_enabled=True, num_successes=0, expect_failures=['check_equalverify', 'check_final_verify'])
    do_test_single("2DUP EQUALVERIFY SHA256 SWAP SHA256 EQUAL NOT",
                   z3_enabled=True, num_successes=0, expect_failures=['check_equalverify', 'check_final_verify'])

    # 160-bit hashes by default are not assumed to be collision-free
    do_test_single("2DUP SHA1 SWAP SHA1 EQUALVERIFY EQUAL NOT",
                   z3_enabled=True, num_successes=1)
    do_test_single("2DUP HASH160 SWAP HASH160 EQUALVERIFY EQUAL NOT",
                   z3_enabled=True, num_successes=1)
    do_test_single("2DUP RIPEMD160 SWAP RIPEMD160 EQUALVERIFY EQUAL NOT",
                   z3_enabled=True, num_successes=1)

    # but with assume_no_160bit_hash_collisions=true, these should fail
    do_test_single("2DUP SHA1 SWAP SHA1 EQUALVERIFY EQUAL NOT",
                   z3_enabled=True, num_successes=0, expect_failures=['check_equalverify', 'check_final_verify'],
                   assume_no_160bit_hash_collisions=True)
    do_test_single("2DUP HASH160 SWAP HASH160 EQUALVERIFY EQUAL NOT",
                   z3_enabled=True, num_successes=0, expect_failures=['check_equalverify', 'check_final_verify'],
                   assume_no_160bit_hash_collisions=True)
    do_test_single("2DUP RIPEMD160 SWAP RIPEMD160 EQUALVERIFY EQUAL NOT",
                   z3_enabled=True, num_successes=0, expect_failures=['check_equalverify', 'check_final_verify'],
                   assume_no_160bit_hash_collisions=True)

    do_test("'a' SHA256INITIALIZE 'b' SHA256UPDATE 'c' SHA256FINALIZE DUP 'abc' SHA256 EQUALVERIFY 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad equal",
            is_tapscript=True)
    do_test("3DUP DUP 'AA' EQUALVERIFY SHA256INITIALIZE SIZE 42 EQUALVERIFY SWAP SHA256UPDATE SIZE 45 EQUALVERIFY SWAP SHA256FINALIZE TOALTSTACK DROP 'BBB' EQUALVERIFY 'CCCC' EQUALVERIFY DROP DROP FROMALTSTACK",
            is_tapscript=True)
    do_test_single("DUP x('00') SWAP CAT SWAP x('0080') EQUALVERIFY IFDUP x('000080') XOR 0 RSHIFT NOT",
                   z3_enabled=True, expect_failures=['check_branch_condition_invalid', 'check_data_too_long', 'check_equalverify'])
    do_test("DUP x('00') SWAP CAT SWAP x('0080') XOR 0 RSHIFT NOT VERIFY IFDUP x('000080') XOR 0 RSHIFT NOT VERIFY",
            num_successes=2)

    do_test("DUP x('0100000000000080') SUB64 VERIFY SWAP 0 SCRIPTNUMTOLE64 EQUALVERIFY x('FFFFFFFFFFFFFF7F') EQUAL",
            is_tapscript=True)
    do_test("INSPECTVERSION LE32TOLE64 LE64TOSCRIPTNUM 1 EQUALVERIFY INSPECTVERSION x('01000000') EQUAL",
            is_tapscript=True)

    do_test("IFDUP NOTIF 1 EQUALVERIFY ENDIF EQUAL",
            num_successes=2, expect_failures=['check_branch_condition_invalid', 'check_data_too_long', 'check_scriptnum_encoding_exceeds_datalen', 'check_scriptnum_minimal_encoding'])

    do_test_single("0 INSPECTOUTPUTVALUE 1 EQUALVERIFY x('0a00000000000700') MUL64 1 EQUALVERIFY",
                   z3_enabled=True, is_tapscript=True, expect_failures=['check_equalverify', 'check_le64_wrong_size'])
    do_test_single("0 INSPECTOUTPUTVALUE 1 EQUALVERIFY x('0a00000000000000') MUL64 1 EQUALVERIFY",
                   z3_enabled=True, is_tapscript=True, expect_failures=['check_equalverify', 'check_le64_wrong_size', 'check_out_of_money_range', 'check_branch_condition_invalid'])

    do_test_single("0 INSPECTOUTPUTVALUE 1 EQUALVERIFY DUP x('0a00000000000100') EQUALVERIFY x('0a00100000000000') MUL64 1 NUMEQUALVERIFY",
                   z3_enabled=False, is_tapscript=True, num_successes=0, expect_failures=['check_invalid_arguments', 'check_numequalverify', 'check_branch_condition_invalid'])
    do_test_single("0 INSPECTOUTPUTVALUE 1 EQUALVERIFY DUP x('0a00000000000100') EQUALVERIFY x('0a00100000000000') MUL64 1 NUMEQUALVERIFY",
                   z3_enabled=True, is_tapscript=True,
                   num_successes=0, expect_failures=['check_int64_out_of_bounds', 'check_le64_wrong_size', 'check_equalverify', 'check_numequalverify', 'check_branch_condition_invalid', 'check_invalid_arguments'])

    do_test("DUP 10 GREATERTHAN IF 10 GREATERTHAN VERIFY ENDIF",
            num_successes=2)

    do_test("SIZE 32 NUMEQUALVERIFY 0 INSPECTOUTPUTSCRIPTPUBKEY -1 NUMEQUALVERIFY EQUALVERIFY",
            is_tapscript=True)

    do_test_single("mul64 1 equalverify",
                   z3_enabled=True, is_tapscript=True, expect_failures=['check_equalverify'])

    do_test_single("MUL64 TOALTSTACK ADD64 FROMALTSTACK VERIFY VERIFY",
                   is_tapscript=True, z3_enabled=False, expect_failures=['check_branch_condition_invalid', 'check_verify'])
    do_test_single("MUL64 TOALTSTACK ADD64 FROMALTSTACK VERIFY VERIFY",
                   is_tapscript=True, z3_enabled=True, expect_failures=['check_branch_condition_invalid', 'check_verify'])

    do_test_single("DUP DUP VERIFY IF VERIFY ELSE 2 ENDIF",
                   z3_enabled=True, expect_failures=['check_branch_condition_invalid', 'check_data_too_long', 'check_verify'])

    failures = do_test_single('$b dup 1 sub not verify 0 $p 1 checkmultisig',
                              z3_enabled=True, expect_failures=['check_checkmultisig_bugbyte_zero', 'check_verify'],
                              is_witness_v0=True, num_successes=0)

    assert 'check_checkmultisig_bugbyte_zero' in failures


if __name__ == '__main__':
    test()
