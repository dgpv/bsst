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

[Root]
------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        WITHIN(wit0, 1, 3) @ END

===============================
Witness usage and model values:
===============================

All valid paths:
----------------
Witnesses used: 1

Model values:
        wit0 : 1
             : 2
             : ---
        # Size = 1

END

echo '1 3 within' | ${BSST} --z3-enabled=true --produce-model-values-for='wit*:3' --report-model-value-sizes=true --log-progress=false > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

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

        NOT(wit0) @ 3:L1
        WITHIN(SIZE(wit0), 1, 3) @ END

===============================
Witness usage and model values:
===============================

All valid paths:
----------------
Witnesses used: 1

Model values:
        wit0 : 0 <encoded: x('00')>
             : 0 <encoded: x('80')>
             : 0 <encoded: x('0000')>
             : 0 <encoded: x('0080')>
             : ---
        # Sizes: 1, 2

END

echo 'size swap not verify 1 3 within' | ${BSST} --z3-enabled=true --produce-model-values-for='wit*:4' --report-model-value-sizes=true --log-progress=false --minimaldata-flag=false --sort-model-values=size_asc > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

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

        NOT(wit0) @ 3:L1
        WITHIN(SIZE(wit0), 1, 3) @ END

===============================
Witness usage and model values:
===============================

All valid paths:
----------------
Witnesses used: 1

Model values:
        wit0 : 0 <encoded: x('00')>
             : 0 <encoded: x('80')>
             : ...
        # Sizes: 1, ...

END

echo 'size swap not verify 1 3 within' | ${BSST} --z3-enabled=true --produce-model-values-for='wit*:2' --report-model-value-sizes=true --log-progress=false --minimaldata-flag=false --sort-model-values=size_asc > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo "SIZE REPORTS TEST SUCCESS"

