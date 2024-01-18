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

        BOOL(ADD(ADD(a1<wit0>, wit1), a2<wit2>)) @ END

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 3

Stack values:
        <result> = ADD(ADD(a1<wit0>, wit1), a2<wit2>) : value_of_sizes(0, 1, 2, 3, 4, 5)

END

cat >${TESTIN} <<END
// bsst-name-alias(wit0): a1
// bsst-name-alias(wit2): a2
ADD ADD
END

cat ${TESTIN} | ${BSST} > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo "NAME ALIASES TEST SUCCESS"

