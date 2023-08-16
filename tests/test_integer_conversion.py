#!/usr/bin/env python3

import struct
import random
from contextlib import contextmanager
from typing import Generator, Callable

import z3

import bsst


@contextmanager
def FreshEnv() -> Generator[None, None, None]:
    env = bsst.SymEnvironment()
    env.z3_enabled = True
    env.use_parallel_solving = False
    env.solver_timeout_seconds = 0

    with bsst.CurrentEnvironment(env):
        bsst.try_import_optional_modules()
        bp = bsst.Branchpoint(pc=0, branch_index=0)
        with bsst.CurrentExecContext(bp.context):
            yield


def test():
    bsst.g_script_body = []

    with FreshEnv():
        seq1 = bsst.FreshConst(bsst.IntSeqSortRef(), 'seq')
        seq2 = bsst.FreshConst(bsst.IntSeqSortRef(), 'seq')
        y = bsst.FreshInt('y')
        x = bsst.FreshInt('x')

    def test_common(*,
                    seq2num: Callable[['z3.SeqSortRef', 'z3.ArithRef'], None],
                    int2bytes: Callable[[int], bytes],
                    min_v: int, max_v: int, max_bytes: int):

        with FreshEnv():
            seq2num(seq1, x)
            seq2num(seq1, y)
            bsst.Check(x == y)
            bsst.z3check(force_check=True)

        with FreshEnv():
            seq2num(seq1, x)
            seq2num(seq2, y)
            bsst.Check(seq1 != seq2)
            bsst.Check(x == y)
            try:
                bsst.z3check(force_check=True)
            except bsst.ScriptFailure as sf:
                assert str(sf).startswith(bsst.SCRIPT_FAILURE_PREFIX_SOLVER)

        for _ in range(100):
            with FreshEnv():
                numbytes = random.randint(1, max_bytes)
                testval = random.randint(min_v, max_v)
                if testval < 0:
                    testval = -(abs(testval) % (1 << (8*numbytes)))
                else:
                    testval = testval % (1 << (8*numbytes))

                testseq = int2bytes(testval)

                bsst.Check(y == testval)
                seq2num(seq1, x)
                bsst.Check(seq1 == bsst.IntSeqVal(testseq))

                model = bsst.z3check(
                    force_check=True,
                    model_values_to_retrieve={'x': (x.decl().name(),
                                                    bsst.SymDataRType.INT)})

                assert model['x'].single_value == testval

                bsst.Check(x != y, bsst.failcode('x')())
                try:
                    bsst.z3check(force_check=True)
                except bsst.ScriptFailure as sf:
                    assert str(sf).startswith(
                        bsst.SCRIPT_FAILURE_PREFIX_SOLVER)

    print("testing scriptnum")
    test_common(
        seq2num=lambda seq, x: bsst.scriptnum_to_sym_integer(seq, x,
                                                             max_size=5),
        int2bytes=lambda x: bsst.integer_to_scriptnum(x),
        min_v=-0x7FFFFFFFFF, max_v=0x7FFFFFFFFF, max_bytes=5)

    print("testing le32 signed")
    test_common(
        seq2num=lambda seq, x: bsst.le32_signed_to_integer(seq, x),
        int2bytes=lambda x: struct.pack('<i', x),
        min_v=-(2**31), max_v=2**31-1, max_bytes=4)

    print("testing le32 unsigned")
    test_common(
        seq2num=lambda seq, x: bsst.le32_unsigned_to_integer(seq, x),
        int2bytes=lambda x: struct.pack('<I', x),
        min_v=0, max_v=2**32-1, max_bytes=4)

    print("testing le64 signed")
    test_common(
        seq2num=lambda seq, x: bsst.le64_signed_to_integer(seq, x),
        int2bytes=lambda x: struct.pack('<q', x),
        min_v=-(2**63), max_v=2**63-1, max_bytes=8)

    print("testing le64 unsigned")
    test_common(
        seq2num=lambda seq, x: bsst.le64_unsigned_to_integer(seq, x),
        int2bytes=lambda x: struct.pack('<Q', x),
        min_v=0, max_v=2**64-1, max_bytes=8)


if __name__ == '__main__':
    test()
