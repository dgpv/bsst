#!/usr/bin/env python3

import sys

from contextlib import contextmanager
from typing import Generator

import bsst

from test_util import CaptureStdout

testcase: list[str] = []
expected_result: list[str] = []
expected_result_z3: list[str] = []

tcstr = """DUP
DUP
DUP
ADD   // =>b1
VERIFY
SWAP
DUP
ADD   // =>x
VERIFY
IF
DUP
ADD // =>z
DUP
VERIFY
ELSE
DUP
ADD // =>b2
DUP
VERIFY
ENDIF
DUP
ADD // =>b3
DUP
ADD // =>b4
VERIFY
TRUE
"""
testcase.append(tcstr)


erstr = """
============
Valid paths:
============

IF wit0 @ 9:L10 : True
----------------------

IF wit0 @ 9:L10 : False
-----------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        BOOL(&b1) @ 4:L5
        BOOL(&x) @ 8:L9
        BOOL(&b4) @ 24:L25
        1 @ END

IF wit0 @ 9:L10 : True
----------------------

        BOOL(&z) @ 13:L14

IF wit0 @ 9:L10 : False
-----------------------

        BOOL(&b2) @ 18:L19

Data references:
----------------
	b1 = x = ADD(wit0, wit0)
	b4 = ADD(&b3, &b3)
	b3 = ADD(&b2, &b2)
	b2 = z = ADD(wit1, wit1)

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 2

"""  # noqa

expected_result.append(erstr)

testcase.append("IF 1 ELSE 2 ENDIF // =>x")

erstr = """
============
Valid paths:
============

IF wit0 @ 0:L1 : True
---------------------

IF wit0 @ 0:L1 : False
----------------------

==============================
Enforced constraints per path:
==============================

IF wit0 @ 0:L1 : True
---------------------

        &x @ END

IF wit0 @ 0:L1 : False
----------------------

        BOOL(&x') @ END

Data references:
----------------
	x = 1
	x' = 2

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 1

"""  # noqa

expected_result.append(erstr)


@contextmanager
def FreshEnv() -> Generator[bsst.SymEnvironment, None, None]:
    env = bsst.SymEnvironment()
    env.use_parallel_solving = False
    env.log_progress = False
    env.solver_timeout_seconds = 0

    with bsst.CurrentEnvironment(env):
        bp = bsst.Branchpoint(pc=0, branch_index=0)
        with bsst.CurrentExecContext(bp.context):
            yield env


def test(testno: int, expres: list[str]) -> None:
    with FreshEnv() as env:
        env.script_info = bsst.parse_script_lines(testcase[testno].split('\n'))

        out: str = ''
        with CaptureStdout() as output:
            bsst.symex_script()
            bsst.report()
            out = output.getvalue()

        if out != expres[testno]:
            print("NO MATCH")
            print("_____________________________________")
            print("Script:")
            print("_____________________________________")
            print(testcase[testno])
            print("_____________________________________")
            print("Expected:")
            print("_____________________________________")
            print(expres[testno])
            print("_____________________________________")
            print("Got:")
            print("_____________________________________")
            print(out)
            print("_____________________________________")
            sys.exit(-1)


if __name__ == '__main__':
    for i in range(len(expected_result)):
        test(i, expected_result)
