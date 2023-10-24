#!/usr/bin/env python3

import re
from contextlib import contextmanager
from typing import Generator, Sequence

import bsst


@contextmanager
def FreshEnv(*, z3_enabled: bool
             ) -> Generator[bsst.SymEnvironment, None, None]:
    env = bsst.SymEnvironment()
    env.z3_enabled = z3_enabled
    with bsst.CurrentEnvironment(env):
        bsst.try_import_optional_modules()
        bp = bsst.Branchpoint(pc=0, branch_index=0)
        with bsst.CurrentExecContext(bp.context):
            yield env


testcases_normal: list[tuple[str, set[int | bytes]]] = [
    (
        """
        // bsst-assume($a): 1 2 3
        $a
        """,
        {1, 2, 3}
    ),
    (
        # NOTE: -4839433545 is beyond 4-byte scriptnum range, but will be
        # included if no arithmetic is performed
        """
        // bsst-assume($a): 100 1000 43345 -245 -3344 -48394 -4839433545
        $a
        """,
        {b'\x64', b'\xe8\x03', b'\x51\xA9\x00',
         b'\xf5\x80', b'\x10\x8d', b'\x0a\xbd\x80', b'\x49\xe5\x73\x20\x81'}
    ),
    (
        # NOTE: -4839433545 is beyond 4-byte scriptnum range, will not
        # be included after arithmetic is done
        """
        // bsst-assume($a): 100 -4839433545
        $a 0 ADD
        """,
        {100}
    ),
    (
        # NOTE: 0x00 must be ignored because it is not valid scriptnum,
        # and we have scriptnums for assume($a), and minimaldat_flag is False
        """
        // bsst-assume($a): >-3 0x00
        // bsst-assume($a): <2
        // bsst-assume($a): !=''
        $a
        """,
        {b'\x81', b'\x82', b'\x01'}
    ),
    (
        """
        // bsst-assume($a): >=-2
        // bsst-assume($a): <=1
        // bsst-assume($a): !=''
        $a
        """,
        {b'\x81', b'\x82', b'\x01'}
    ),
    (
        # combined via AND, and thus '' must be the only possible value
        """
        // bsst-assume($a): >=-2
        // bsst-assume($a): <=1
        // bsst-assume($a): =''
        $a
        // bsst-assert: 0
        """,
        {b''}
    ),
    (
        """
        // bsst-assume($a): -1..2
        $a
        """,
        {-1, 0, 1, 2}
    ),
    (
        """
        // bsst-assume($a): le64(-1)..le64(2)
        $a
        """,
        set(bsst.IntLE64.from_int(v) for v in (-1, 0, 1, 2))
    ),
    (
        """
        // bsst-assume($a): x('efcdab99')
        $a 0x78563412 CAT
        // bsst-assert: le64(1311768467445894639)
        """,
        {bsst.IntLE64.from_int(0x1234567899ABCDEF)}
    ),
    (
        """
        // bsst-assume($a): 'abc'
        $a 'def' CAT
        // bsst-assert: 'abcdef'
        """,
        {b'abcdef'}
    ),
    (
        """
        // bsst-assume($a): 19
        // bsst-assume($b): 0 1 2 3
        $a $b ADD DUP 22 NUMEQUAL NOT VERIFY DUP 19 NUMEQUAL NOT VERIFY
        // bsst-assert: 20 21
        // bsst-assert: <22
        // bsst-assert: !=19
        """,
        {20, 21}
    ),
    (
        """
        // bsst-assume($a): le64(19) le64(21)
        $a le64(1) ADD64 VERIFY le64(2) DIV64 VERIFY
        // bsst-assert: le64(10) le64(11) !=le64(12)
        """,
        {bsst.IntLE64.from_int(10), bsst.IntLE64.from_int(11)}
    ),
    (
        """
        // bsst-assume($a): le64(20) le64(21)
        $a DUP
        le64(1) ADD64 VERIFY le64(3) DIV64 VERIFY
        SWAP // =>remainder
        le64(0) EQUAL VERIFY
        // bsst-assert(&remainder): le64(0)
        // bsst-assert-size(&remainder): 8
        // bsst-assert: le64(7)
        // bsst-assert-size: 8
        DROP
        """,
        {bsst.IntLE64.from_int(20)}
    ),
    (
        """
        10 5 DUP ADD SUB
        // bsst-assert-size: 0
        1 ADD
        // bsst-assert: 1
        """,
        {1}
    ),
    (
        """
        $a // =>a
        // bsst-assume-size($a): 1
        DUP x('01') CAT
        // bsst-assert-size: 2
        1 ADD 258 NUMEQUALVERIFY
        // bsst-assert(&a): 1
        """,
        {1}
    ),
    (
        """
        DUP TOALTSTACK
        CHECKSIGVERIFY
        // bsst-assert-size(wit0): 32
        // bsst-assert-size(wit1): 64 65
        FROMALTSTACK SIZE
        """,
        {32}
    ),
]

testcases_assnfail: list[tuple[str, set[int], bool]] = [
    (
        # conflicting assumption constraints
        """
        // bsst-assume($a): 100 1000 43345 -245 -3344 -48394 -4839433545
        // bsst-assume($a): 3
        $a
        """,
        {2, 3}, False
    ),
    (
        """
        // bsst-assume($a): 100 -4839433545
        $a 0 ADD
        // bsst-assert: 1
        """,
        {4}, False
    ),
    (
        """
        // bsst-assume($a): >-3 0x00
        // bsst-assume($a): <2
        // bsst-assume($a): !=''
        $a
        // bsst-assert-size: 0
        """,
        {6}, False
    ),
    (
        """
        // bsst-assume($a): >=-2
        // bsst-assume($a): <=1
        // bsst-assume($a): =''
        $a
        // bsst-assert: !=0
        """,
        {6}, False
    ),
    (
        """
        // bsst-assume($a): -1..2
        $a
        // bsst-assert: -3..-2
        """,
        {4}, False
    ),
    (
        """
        // bsst-assume($a): le64(-1)..le64(2)
        $a
        // bsst-assert: le64(-4)..le64(-2)
        """,
        {4}, False
    ),
    (
        """
        // bsst-assume($a): x('efcdab99')
        $a 0x78563412 CAT
        // bsst-assert: le64(123)
        """,
        {4}, False
    ),
    (
        """
        // bsst-assume($a): 'abc'
        $a 'def' CAT
        // bsst-assert: 'ABCDEF'
        """,
        {4}, False
    ),
    (
        """
        // bsst-assume($a): 19
        // bsst-assume($b): 0 1 2 3
        $a $b ADD DUP 22 NUMEQUAL NOT VERIFY DUP 19 NUMEQUAL NOT VERIFY
        // bsst-assert: 20 21
        // bsst-assert: <22
        // bsst-assert: =19
        """,
        {7}, False
    ),
    (
        """
        // bsst-assume($a): le64(19) le64(21)
        $a le64(1) ADD64 VERIFY le64(2) DIV64 VERIFY
        // bsst-assert: le64(10) le64(11) !=le64(12)
        // bsst-assert: =le64(12)
        """,
        {5}, False
    ),
    (
        """
        // bsst-assume($a): le64(20) le64(21)
        $a DUP
        le64(1) ADD64 VERIFY le64(3) DIV64 VERIFY
        SWAP // =>remainder
        le64(0) EQUAL VERIFY
        // bsst-assert(&remainder): le64(0)
        // bsst-assert-size(&remainder): 8
        // bsst-assert: le64(4)
        // bsst-assert-size: 8
        DROP
        """,
        {9}, False
    ),
    (
        """
        10 5 DUP ADD SUB
        // bsst-assert-size: 1
        1 ADD
        // bsst-assert: 1
        """,
        {3}, False
    ),
    (
        """
        $a // =>a
        // bsst-assume-size($a): 1
        DUP x('01') CAT
        // bsst-assert-size: 2
        1 ADD 258 NUMEQUALVERIFY
        // bsst-assert(&a): 0x00
        """,
        {7}, False
    ),
    (
        """
        DUP
        IF
        // bsst-assert-size: >0
        DUP 1 GREATERTHANOREQUAL VERIFY
        ELSE
        // bsst-assert-size: 1
        SIZE 10 NUMEQUALVERIFY
        ENDIF
        // bsst-assert(wit0): 1
        // bsst-assert: >10
        """,
        {7, 11}, True
    ),
    (
        """
        DUP
        IF
        // bsst-assert-size: >0
        DUP 1 GREATERTHANOREQUAL VERIFY
        ELSE
        // bsst-assert-size: 1
        SIZE 10 NUMEQUALVERIFY
        ENDIF
        // bsst-assert: >0
        // bsst-assert(wit0): 0
        """,
        {7, 11}, True
    ),
    (
        # tapscript signature is 32 bytes, so first assertion musr fail
        """
        CHECKSIGVERIFY
        // bsst-assert-size(wit0): 33
        // bsst-assert-size(wit1): 64
        """,
        {3}, False
    ),
    (
        # signature can be 64 or 65 bytes, so second assertion musr fail
        """
        CHECKSIGVERIFY
        // bsst-assert-size(wit0): 32
        // bsst-assert-size(wit1): 64
        """,
        {4}, False
    ),
]

testcases_otherfail: list[str] = [
    # no mixing of le64 and scriptnums
    """
    // bsst-assume($a): 100 101
    // bsst-assume($a): le64(100)
    $a
    """,
    """
    // bsst-assume($a): le64(100)
    $a
    // bsst-assert: 100
    """,
    # no asserts against empty stack
    """
    // bsst-assert: 0
    1
    """,
    # no spaces allowed inside expression
    """
    1
    // bsst-assert: >= 0
    """,
    """
    le64(1)
    // bsst-assert: le64( 1 )
    """,
    # range end must be > start
    """
    1
    // bsst-assert: 1..1
    """,
    """
    1
    // bsst-assert: 2..1
    """,
    # non-witness name for bsst-assert name without &
    """
    1 // =>wit
    // bsst-assert(wit): 1
    """
]


def test_assn_normal(
    tc_no: int, tc_text: str, tc_expected_values: set[int | bytes]
) -> None:

    if tc_expected_values:
        assert all(isinstance(v, type(tuple(tc_expected_values)[0]))
                   for v in tc_expected_values), "mixed types are not allowed"

    is_ok = False

    with FreshEnv(z3_enabled=True) as env:
        env.use_parallel_solving = False
        env.log_progress = False
        env.is_elements = True
        env.is_incomplete_script = True
        env.solver_timeout_seconds = 0

        def post_finalize_hook(ctx: bsst.ExecContext,
                               env: bsst.SymEnvironment) -> None:
            nonlocal is_ok

            mvals: Sequence[int | bytes]

            top = ctx.stack[-1]

            if tc_expected_values and \
                    isinstance(tuple(tc_expected_values)[0], int):
                if top.is_static:
                    mvals = [top.as_scriptnum_int()]
                else:
                    top.use_as_Int(max_size=5)
                    mvals = ctx.stack[-1].collect_integer_model_values(
                        max_count=len(tc_expected_values)+1)
            else:
                if top.is_static:
                    mvals = [top.as_bytes()]
                else:
                    ctx.stack[-1].use_as_ByteSeq()
                    mvals = ctx.stack[-1].collect_byte_model_values(
                        max_count=len(tc_expected_values)+1)

            assert len(mvals) == len(set(mvals)), \
                ("no duplicates expected", mvals)
            assert set(mvals) == tc_expected_values, \
                ("model values must match expected values", mvals)

            print("OK")

            is_ok = True

        env.script_info = bsst.get_opcodes(tc_text.split('\n'))
        env.post_finalize_hook = post_finalize_hook

        bsst.symex_script()

        assert is_ok, "post_finalize_hook must run and successfully return"


def test_assn_failing(
    tc_no: int, tc_text: str, failure_lines: set[int], is_exact_match: bool
) -> None:

    with FreshEnv(z3_enabled=True) as env:
        env.use_parallel_solving = False
        env.log_progress = False
        env.is_elements = True
        env.is_incomplete_script = True
        env.solver_timeout_seconds = 0

        env.script_info = bsst.get_opcodes(tc_text.split('\n'))

        bsst.symex_script()

        seen_failure_lines: set[int] = set()

        def search_failures(ctx: bsst.ExecContext) -> None:
            if not ctx.failure:
                return

            flines: set[int] = set()
            pc, errstr = ctx.failure
            if errstr.startswith(bsst.SCRIPT_FAILURE_PREFIX_SOLVER):
                for code, pc in bsst.parse_failcodes(errstr):
                    m = re.match('check_(assumption|assertion)_at_line_(\\d+)',
                                 code)
                    assert m, (f'assertion or assumption failure expected, '
                               f'but got "{code}"')
                    fl = int(m.group(2))
                    flines.add(fl)
            else:
                m = re.match('assertion failed at line (\\d+)', errstr)
                assert m, (f'assertion or assumption failure expected, '
                           f'but got "{errstr}"')
                fl = int(m.group(1))
                flines.add(fl)

            assert flines.issubset(failure_lines), (flines, failure_lines)
            seen_failure_lines.update(flines)

        env.get_root_branch().walk_contexts(search_failures,
                                            include_failed=True)

        assert seen_failure_lines, "at least one failure must be detected"
        assert seen_failure_lines.issubset(failure_lines)
        if is_exact_match:
            assert seen_failure_lines == failure_lines, \
                ("exact match expected", seen_failure_lines, failure_lines)

        print("OK")


def test_other_failing(tc_no: int, tc_text: str) -> None:

    with FreshEnv(z3_enabled=True) as env:
        env.use_parallel_solving = False
        env.log_progress = False
        env.is_elements = True
        env.is_incomplete_script = True
        env.solver_timeout_seconds = 0

        try:
            env.script_info = bsst.get_opcodes(tc_text.split('\n'))
        except bsst.BSSTParsingError:
            print("OK")
            return

        assert False, "BSSTParsingError expected"


if __name__ == '__main__':
    for tc_no, (tc_text, tc_expected_values) in enumerate(testcases_normal):
        print("TESTCASE ASSN NORMAL", tc_no+1, end=' ')
        test_assn_normal(tc_no, tc_text, tc_expected_values)

    for tc_no, (tc_text, failure_lines, is_exact_match) in \
            enumerate(testcases_assnfail):
        print("TESTCASE ASSN FAILING", tc_no+1, end=' ')
        test_assn_failing(tc_no, tc_text, failure_lines, is_exact_match)

    for tc_no, tc_text in enumerate(testcases_otherfail):
        print("TESTCASE OTHER FAILING", tc_no+1, end=' ')
        test_other_failing(tc_no, tc_text)
