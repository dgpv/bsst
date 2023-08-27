#!/usr/bin/env python3

import sys

from io import StringIO

from contextlib import contextmanager
from typing import Generator

import bsst

testcase1 = """DUP
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

expected_result = """============
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

        BOOL(b1) @ 4:L5
        BOOL(x) @ 8:L9
        BOOL(b4) @ 24:L25
        BOOL(1) @ END

IF wit0 @ 9:L10 : True
----------------------

        BOOL(z) @ 13:L14

IF wit0 @ 9:L10 : False
-----------------------

        BOOL(b2) @ 18:L19

Where:
------
	b1 = x = ADD(wit0, wit0)
	b4 = ADD(b3, b3)
	b3 = ADD(b2, b2)
	b2 = z = ADD(wit1, wit1)

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 2

"""  # noqa


with_z3_result = """============
Valid paths:
============

IF wit0 @ 9:L10 : True
----------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        <*> BOOL(b1) @ 4:L5
        <*> BOOL(x) @ 8:L9
        <*> BOOL(z) @ 13:L14
        <*> BOOL(b4) @ 24:L25
        BOOL(1) @ END

Where:
------
	b1 = x = ADD(wit0, wit0)
	z = ADD(wit1, wit1)
	b4 = ADD(b3, b3)
	b3 = ADD(z, z)

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 2

==================
Failures per path:
==================

IF wit0 @ 9:L10 : False
-----------------------
Detected at IF @ 9:L10

One of:
~~~~~~~
IF @ 9:L10: check_branch_condition_invalid

  stack:
	wit0

  vfExec: [False]

VERIFY @ 8:L9: check_verify

  stack:
	ADD(wit0, wit0)
	wit0

Enforcements before failure was detected:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

	BOOL(b1) @ 4:L5
	BOOL(x) @ 8:L9

Where:
------
	b1 = x = ADD(wit0, wit0)

"""  # noqa


@contextmanager
def CaptureStdout() -> Generator[StringIO, None, None]:
    save_stdout = sys.stdout
    out = StringIO()
    sys.stdout = out
    yield out
    sys.stdout = save_stdout


@contextmanager
def FreshEnv() -> Generator[None, None, None]:
    env = bsst.SymEnvironment()
    env.use_parallel_solving = False
    env.log_progress = False
    env.solver_timeout_seconds = 0

    with bsst.CurrentEnvironment(env):
        bsst.try_import_optional_modules()
        bp = bsst.Branchpoint(pc=0, branch_index=0)
        with bsst.CurrentExecContext(bp.context):
            yield


def test() -> None:
    with FreshEnv():
        (bsst.g_script_body,
         bsst.g_line_no_table,
         bsst.g_var_save_positions) = bsst.get_opcodes(testcase1.split('\n'))

        out: str = ''
        with CaptureStdout() as output:
            bsst.g_is_in_processing = True
            bsst.symex_script()
            bsst.g_is_in_processing = False
            bsst.report()
            out = output.getvalue()

        if out != expected_result:
            print("NO MATCH")
            print("Expected:")
            print("_____________________________________")
            print(expected_result)
            print("_____________________________________")
            print("Got:")
            print("_____________________________________")
            print(out)
            print("_____________________________________")
            sys.exit(-1)


if __name__ == '__main__':
    test()
