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

IF wit3 @ 4:L3 : True
IF wit3 @ 14:L9 : True
----------------------

IF wit3 @ 4:L3 : False
IF wit3 @ 14:L9 : False
-----------------------

==============================
Enforced constraints per path:
==============================

IF wit3 @ 4:L3 : True
---------------------

        EQUAL(1, wit2) @ END

IF wit3 @ 4:L3 : False
----------------------

        EQUAL(2, wit1) @ END

==============
Unused values:
==============

IF wit3 @ 4:L3 : True
---------------------
        wit1 from 1:L1

IF wit3 @ 4:L3 : False
----------------------
        wit2 from 2:L1

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 4

IF wit3 @ 4:L3 : True
---------------------

Stack values:
        <result> = EQUAL(1, wit2) : one_of(0, 1)

IF wit3 @ 4:L3 : False
----------------------

Stack values:
        <result> = EQUAL(2, wit1) : one_of(0, 1)

==================
Warnings per path:
==================

IF wit3 @ 4:L3 : True
---------------------
        Altstack length is 1 @ END

IF wit3 @ 4:L3 : False
----------------------
        Altstack length is 1 @ END

==================
Failures per path:
==================

IF wit3 @ 4:L3 : True
IF wit3 @ 14:L9 : False
-----------------------
IF @ 14:L9: check_branch_condition_invalid

  stack:
        wit3
        wit2

  altstack:
        wit0

IF wit3 @ 4:L3 : False
IF wit3 @ 14:L9 : True
----------------------
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

IF wit0 @ 0:L1 : True
---------------------

IF wit0 @ 0:L1 : False
----------------------

==============================
Enforced constraints per path:
==============================

IF wit0 @ 0:L1 : True
---------------------

        1 @ END

IF wit0 @ 0:L1 : False
----------------------

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

IF wit0 @ 0:L1 : True
---------------------
Witnesses used: 2

Stack values:
        <result> = 1

IF wit0 @ 0:L1 : False
----------------------
Witnesses used: 2

Stack values:
        <result> = 2

END

echo 'if 1 else 2 endif swap drop' | ${BSST} >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo "UNUSED VALUE DETECTION TEST SUCCESS"
