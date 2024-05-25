#!/usr/bin/env python3

import sys

from contextlib import contextmanager
from typing import Generator, Any

import bsst

from test_util import CaptureStdout

testcase: list[str] = []
expected_result: list[str] = []
expected_result_z3: list[str] = []
settings: list[dict[str, Any]] = []

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

When wit0 = 1 :: [IF @ 9:L10]
-----------------------------

When wit0 = 0 :: [IF @ 9:L10]
-----------------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        BOOL(&b1) @ 4:L5
        BOOL(&x) @ 8:L9
        BOOL(&b4) @ 24:L25
        1 @ END

When wit0 = 1 :: [IF @ 9:L10]
-----------------------------

        BOOL(&z) @ 13:L14

When wit0 = 0 :: [IF @ 9:L10]
-----------------------------

        BOOL(&b2) @ 18:L19

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 2

Stack values:
        <result> = 1

================
Data references:
================

        b1 = x = ADD(wit0, wit0)
        z = b2 = ADD(wit1, wit1)
        b3 = ADD(&z, &z)
        b4 = ADD(&b3, &b3)

"""  # noqa

expected_result.append(erstr)
settings.append({})

testcase.append(tcstr)
settings.append({'tag_enforcements_with_position': True})

expected_result.append("""
============
Valid paths:
============

When wit0 = 1 :: [IF @ 9:L10]
-----------------------------

When wit0 = 0 :: [IF @ 9:L10]
-----------------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        BOOL(&b1) @ 4:L5
        BOOL(&x) @ 8:L9
        BOOL(&b4) @ 24:L25
        1 @ END

When wit0 = 1 :: [IF @ 9:L10]
-----------------------------

        BOOL(&z) @ 13:L14

When wit0 = 0 :: [IF @ 9:L10]
-----------------------------

        BOOL(&b2) @ 18:L19

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 2

Stack values:
        <result> = 1

================
Data references:
================

        b1 = x = ADD(wit0, wit0)
        z = b2 = ADD(wit1, wit1)
        b3 = ADD(&z, &z)
        b4 = ADD(&b3, &b3)

""")


testcase.append("IF 1 ELSE 2 ENDIF // =>x")

erstr = """
============
Valid paths:
============

When wit0 = 1 :: [IF @ 0:L1]
----------------------------

When wit0 = 0 :: [IF @ 0:L1]
----------------------------

==============================
Enforced constraints per path:
==============================

When wit0 = 1 :: [IF @ 0:L1]
----------------------------

        &x @ END

When wit0 = 0 :: [IF @ 0:L1]
----------------------------

        BOOL(&x') @ END

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 1

When wit0 = 1 :: [IF @ 0:L1]
----------------------------
Witnesses used: 1

Stack values:
        <result> = &x = 1

When wit0 = 0 :: [IF @ 0:L1]
----------------------------
Witnesses used: 1

Stack values:
        <result> = &x' = 2

================
Data references:
================

        x = 1
        x' = 2

"""  # noqa

expected_result.append(erstr)
settings.append({})

testcase.append("""if
    1 $x add swap
    if
        // =>a
    else
        drop 1 $x add
    endif
else
    if
        1 $x add // =>b
    else
        1 $x add // =>c
    endif
    not
endif
""")

erstr = """
============
Valid paths:
============

When wit0 = 1 :: [IF @ 0:L1]
 And wit1 = 1 :: [IF @ 5:L3]
----------------------------

When wit0 = 1 :: [IF @ 0:L1]
 And wit1 = 0 :: [IF @ 5:L3]
----------------------------

When wit0 = 0 :: [IF @ 0:L1]
 And wit1 = 1 :: [IF @ 13:L9]
-----------------------------

When wit0 = 0 :: [IF @ 0:L1]
 And wit1 = 0 :: [IF @ 13:L9]
-----------------------------

==============================
Enforced constraints per path:
==============================

When wit0 = 1 :: [IF @ 0:L1]
----------------------------

        BOOL(&{a}) @ END

When wit0 = 0 :: [IF @ 0:L1]
----------------------------

        NOT(&{b;c}) @ END

==============
Unused values:
==============

When wit0 = 1 :: [IF @ 0:L1]
 And wit1 = 0 :: [IF @ 5:L3]
----------------------------
        &a from 3:L2

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 2

When wit0 = 1 :: [IF @ 0:L1]
----------------------------

Stack values:
        <result> = ADD($x, 1) : value_of_sizes(0, 1, 2, 3, 4, 5)

When wit0 = 0 :: [IF @ 0:L1]
----------------------------

Stack values:
        <result> = NOT(ADD($x, 1)) : one_of(0, 1)

When wit0 = 1 :: [IF @ 0:L1]
 And wit1 = 1 :: [IF @ 5:L3]
----------------------------
Witnesses used: 2

Stack values:
        <result> = ADD($x, 1) = &a : value_of_sizes(0, 1, 2, 3, 4, 5)

================
Data references:
================

        a = b = c = ADD($x, 1)

"""  # noqa

expected_result.append(erstr)
settings.append({})


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
        for setting, setting_value in settings[testno].items():
            setattr(env, setting, setting_value)

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
