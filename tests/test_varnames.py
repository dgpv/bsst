#!/usr/bin/env python3

import sys

from io import StringIO

from contextlib import contextmanager
from typing import Generator

import bsst

testcase1 = """
DUP
DUP
DUP
ADD   // =>b
VERIFY
SWAP
DUP
ADD   // =>x
VERIFY
IF
DUP
ADD // =>z
ELSE
DUP
ADD // =>b
ENDIF
DUP
ADD // =>b
DUP
ADD // =>b
VERIFY
TRUE
"""

expected_result = """============
Valid paths:
============

IF wit0 @ 9:L11 : True
----------------------
IF wit0 @ 9:L11 : False
-----------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        b @ 4:L6
        x @ 8:L10
        b @ 20:L22
        1 @ END

Where:
------
	b = x = ADD(wit0, wit0)
	b' = ADD(b, b)
	b'' = ADD(b, b)
	b''' = z = ADD(wit1, wit1)

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 2

"""  # noqa


with_z3_result = """============
Valid paths:
============

IF wit0 @ 9:L11 : True
----------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        <*> b @ 4:L6
        <*> x @ 8:L10
        b @ 20:L22
        1 @ END

Where:
------
	b = x = ADD(wit0, wit0)
	b' = ADD(b, b)
	b'' = ADD(z, z)
	z = ADD(wit1, wit1)

===================================================
Witness usage and model values for all valid paths:
===================================================
Witnesses used: 2
Stack:
	wit0 = 1
	wit1 : -536870911

	<result> = 1

==================
Failures per path:
==================

IF wit0 @ 9:L11 : False
-----------------------
Detected at IF @ 9:L11

One of:
~~~~~~~
IF @ 9:L11: check_branch_condition_invalid

  stack:
	wit0

  vfExec: [False]

VERIFY @ 8:L10: check_verify

  stack:
	ADD(wit0, wit0)
	wit0

Enforcements before failure was detected:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

	b @ 4:L6
	x @ 8:L10

Where:
------
	b = x = ADD(wit0, wit0)


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
