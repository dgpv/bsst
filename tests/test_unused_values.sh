#!/usr/bin/env bash

set -ex

TESTIN=`mktemp`
TESTOUT=`mktemp`
TESTEXPECTED=`mktemp`

BSST=bsst/__init__.py

function cleanup() {
    rm -f ${TESTIN}
    rm -f ${TESTOUT}
    rm -f ${TESTEXPECTED}
}

trap cleanup EXIT

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

When wit3 :: [IF @ 4:L3]
 And wit3 :: [IF @ 14:L9]
-------------------------

When not wit3 :: [IF @ 4:L3]
 And not wit3 :: [IF @ 14:L9]
-----------------------------

==============================
Enforced constraints per path:
==============================

When wit3 :: [IF @ 4:L3]
------------------------

        EQUAL(1, wit2) @ END

When not wit3 :: [IF @ 4:L3]
----------------------------

        EQUAL(2, wit1) @ END

==============
Unused values:
==============

When wit3 :: [IF @ 4:L3]
------------------------
        wit1 from 1:L1

When not wit3 :: [IF @ 4:L3]
----------------------------
        wit2 from 2:L1

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 4

When wit3 :: [IF @ 4:L3]
------------------------

Stack values:
        <result> = EQUAL(1, wit2) : one_of(0, 1)

When not wit3 :: [IF @ 4:L3]
----------------------------

Stack values:
        <result> = EQUAL(2, wit1) : one_of(0, 1)

==================
Warnings per path:
==================

When wit3 :: [IF @ 4:L3]
------------------------
        Altstack length is 1 @ END

When not wit3 :: [IF @ 4:L3]
----------------------------
        Altstack length is 1 @ END

==================
Failures per path:
==================

When wit3 :: [IF @ 4:L3]
 And not wit3 :: [IF @ 14:L9]
-----------------------------
IF @ 14:L9: check_branch_condition_invalid

  stack:
        wit3
        wit2

  altstack:
        wit0

When not wit3 :: [IF @ 4:L3]
 And wit3 :: [IF @ 14:L9]
----------------------------
IF @ 14:L9: check_branch_condition_invalid

  stack:
        wit3
        wit1

  altstack:
        wit0

END

cat >${TESTIN} <<END
toaltstack toaltstack toaltstack
dup
if
    fromaltstack fromaltstack drop
else
    fromaltstack drop fromaltstack
endif
swap
if 1 else 2 endif equal
END

cat ${TESTIN} | ${BSST} >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

When wit0 :: [IF @ 0:L1]
------------------------

When not wit0 :: [IF @ 0:L1]
----------------------------

==============================
Enforced constraints per path:
==============================

When wit0 :: [IF @ 0:L1]
------------------------

        1 @ END

When not wit0 :: [IF @ 0:L1]
----------------------------

        BOOL(2) @ END

==============
Unused values:
==============

All valid paths:
----------------
        wit1 from 5:L1

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 2

When wit0 :: [IF @ 0:L1]
------------------------
Witnesses used: 2

Stack values:
        <result> = 1

When not wit0 :: [IF @ 0:L1]
----------------------------
Witnesses used: 2

Stack values:
        <result> = 2

END

echo 'if 1 else 2 endif swap drop' | ${BSST} >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo "UNUSED VALUE DETECTION TEST SUCCESS"
