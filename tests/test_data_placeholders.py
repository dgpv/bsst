#!/usr/bin/env python3

import sys

from io import StringIO

from contextlib import contextmanager
from typing import Generator

import bsst

testcase = """
$a 1 add
$a 2 add 1 sub
equal
"""


expected_result = """
============
Valid paths:
============

[Root]
------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        <*> EQUAL(ADD($a, 1), SUB(ADD($a, 2), 1)) @ END

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 0

"""


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
    env.z3_enabled = True
    env.produce_model_values = False

    with bsst.CurrentEnvironment(env):
        bsst.try_import_optional_modules()
        bp = bsst.Branchpoint(pc=0, branch_index=0)
        with bsst.CurrentExecContext(bp.context):
            yield


def test() -> None:
    with FreshEnv():
        (bsst.g_script_body,
         bsst.g_line_no_table,
         bsst.g_var_save_positions) = bsst.get_opcodes(testcase.split('\n'))

        out: str = ''
        with CaptureStdout() as output:
            bsst.g_is_in_processing = True
            bsst.symex_script()
            bsst.g_is_in_processing = False
            bsst.report()
            out = output.getvalue()

        if out != expected_result:
            print("NO MATCH")
            print("_____________________________________")
            print("Script:")
            print("_____________________________________")
            print(testcase)
            print("_____________________________________")
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
