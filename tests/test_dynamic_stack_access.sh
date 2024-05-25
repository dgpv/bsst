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

=====================================================
NOTE: There are execution paths that was not explored
=====================================================

============
Valid paths:
============

When wit0 = 0 :: [PICK @ 0:L1]
------------------------------

When wit0 = 1 :: [PICK @ 0:L1]
------------------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

When wit0 = 0 :: [PICK @ 0:L1]
------------------------------
Witnesses used: 2

Model values:
        wit0 : 0
        wit1 : ?

Stack values:
        stack[-1] = wit1 : ...
        stack[-2] = wit1 : ...

When wit0 = 1 :: [PICK @ 0:L1]
------------------------------
Witnesses used: 3

Model values:
        wit0 = 1
        wit1 : ?
        wit2 : ?

Stack values:
        stack[-1] = wit2 : ...
        stack[-2] = wit1 : ...
        stack[-3] = wit2 : ...

==================
Failures per path:
==================

When wit0 = 2, ... :: [PICK @ 0:L1]
-----------------------------------
The path was not explored

END

echo 'pick' | ${BSST} --z3-enabled=true --is-incomplete-script=true --max-samples-for-dynamic-stack-access=2 --log-progress=false >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

=====================================================
NOTE: There are execution paths that was not explored
=====================================================

============
Valid paths:
============

When wit0 = 0 :: [ROLL @ 0:L1]
------------------------------

When wit0 = 1 :: [ROLL @ 0:L1]
------------------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

When wit0 = 0 :: [ROLL @ 0:L1]
------------------------------
Witnesses used: 2

Model values:
        wit0 : 0
        wit1 : ?

Stack values:
        stack[-1] = wit1 : ...

When wit0 = 1 :: [ROLL @ 0:L1]
------------------------------
Witnesses used: 3

Model values:
        wit0 = 1
        wit1 : ?
        wit2 : ?

Stack values:
        stack[-1] = wit2 : ...
        stack[-2] = wit1 : ...

==================
Failures per path:
==================

When wit0 = 2, ... :: [ROLL @ 0:L1]
-----------------------------------
The path was not explored

END

echo 'roll' | ${BSST} --z3-enabled=true --is-incomplete-script=true --max-samples-for-dynamic-stack-access=2 --log-progress=false >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

When &a = 1 :: [PICK @ 5:L3]
----------------------------

When &a = 2 :: [PICK @ 5:L3]
----------------------------

When &a = 3 :: [PICK @ 5:L3]
----------------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        <*> WITHIN(&a, 1, 4) @ 4:L1

===============================
Witness usage and model values:
===============================

All valid paths:
----------------

Model values:
        wit0 = &a : ...

When &a = 1 :: [PICK @ 5:L3]
----------------------------
Witnesses used: 3

Model values:
        wit0 = &a = 1
        wit1 : ?
        wit2 : ?

Stack values:
        stack[-1] = wit2 : ...
        stack[-2] = wit1 : ...
        stack[-3] = wit2 : ...

When &a = 2 :: [PICK @ 5:L3]
----------------------------
Witnesses used: 4

Model values:
        wit0 = &a = 2
        wit1 : ?
        wit2 : ?
        wit3 : ?

Stack values:
        stack[-1] = wit3 : ...
        stack[-2] = wit1 : ...
        stack[-3] = wit2 : ...
        stack[-4] = wit3 : ...

When &a = 3 :: [PICK @ 5:L3]
----------------------------
Witnesses used: 5

Model values:
        wit0 = &a = 3
        wit1 : ?
        wit2 : ?
        wit3 : ?
        wit4 : ?

Stack values:
        stack[-1] = wit4 : ...
        stack[-2] = wit1 : ...
        stack[-3] = wit2 : ...
        stack[-4] = wit3 : ...
        stack[-5] = wit4 : ...

================
Data references:
================

        a = wit0

END

cat >${TESTIN} <<END
dup 1 4 within verify
// =>a
pick
END

cat ${TESTIN} | ${BSST} --z3-enabled=true --is-incomplete-script=true --max-samples-for-dynamic-stack-access=4 --produce-model-values-for='*' --log-progress=false >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

When &a = 1 :: [ROLL @ 5:L3]
----------------------------

When &a = 2 :: [ROLL @ 5:L3]
----------------------------

When &a = 3 :: [ROLL @ 5:L3]
----------------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        <*> WITHIN(&a, 1, 4) @ 4:L1

===============================
Witness usage and model values:
===============================

All valid paths:
----------------

Model values:
        wit0 = &a : ...

When &a = 1 :: [ROLL @ 5:L3]
----------------------------
Witnesses used: 3

Model values:
        wit0 = &a = 1
        wit1 : ?
        wit2 : ?

Stack values:
        stack[-1] = wit2 : ...
        stack[-2] = wit1 : ...

When &a = 2 :: [ROLL @ 5:L3]
----------------------------
Witnesses used: 4

Model values:
        wit0 = &a = 2
        wit1 : ?
        wit2 : ?
        wit3 : ?

Stack values:
        stack[-1] = wit3 : ...
        stack[-2] = wit1 : ...
        stack[-3] = wit2 : ...

When &a = 3 :: [ROLL @ 5:L3]
----------------------------
Witnesses used: 5

Model values:
        wit0 = &a = 3
        wit1 : ?
        wit2 : ?
        wit3 : ?
        wit4 : ?

Stack values:
        stack[-1] = wit4 : ...
        stack[-2] = wit1 : ...
        stack[-3] = wit2 : ...
        stack[-4] = wit3 : ...

================
Data references:
================

        a = wit0

END

cat >${TESTIN} <<END
dup 1 4 within verify
// =>a
roll
END

cat ${TESTIN} | ${BSST} --z3-enabled=true --is-incomplete-script=true --max-samples-for-dynamic-stack-access=4 --produce-model-values-for='*' --log-progress=false >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

=====================================================
NOTE: There are execution paths that was not explored
=====================================================

============
Valid paths:
============

When wit0 = 0 as num_keys :: [CHECKMULTISIG @ 0:L1]
---------------------------------------------------

When wit0 = 1 as num_keys :: [CHECKMULTISIG @ 0:L1]
 And wit2 = 0 as num_signatures :: [CHECKMULTISIG @ 0:L1]
---------------------------------------------------------

When wit0 = 1 as num_keys :: [CHECKMULTISIG @ 0:L1]
 And wit2 = 1 as num_signatures :: [CHECKMULTISIG @ 0:L1]
---------------------------------------------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

When wit0 = 0 as num_keys :: [CHECKMULTISIG @ 0:L1]
---------------------------------------------------
Witnesses used: 3

Model values:

Stack values:
        stack[-1] = CHECKMULTISIG(wit0, wit1) = 1

When wit0 = 1 as num_keys :: [CHECKMULTISIG @ 0:L1]
---------------------------------------------------

Model values:
        wit0 = 1

When wit0 = 1 as num_keys :: [CHECKMULTISIG @ 0:L1]
 And wit2 = 0 as num_signatures :: [CHECKMULTISIG @ 0:L1]
---------------------------------------------------------
Witnesses used: 4

Model values:

Stack values:
        stack[-1] = CHECKMULTISIG(wit0, wit1, wit2) = 1

When wit0 = 1 as num_keys :: [CHECKMULTISIG @ 0:L1]
 And wit2 = 1 as num_signatures :: [CHECKMULTISIG @ 0:L1]
---------------------------------------------------------
Witnesses used: 5

Model values:
        wit2 = 1

Stack values:
        stack[-1] = CHECKMULTISIG(wit0, wit1, wit2, wit3) : 0

==================
Failures per path:
==================

When wit0 = 2, ... as num_keys :: [CHECKMULTISIG @ 0:L1]
--------------------------------------------------------
The path was not explored

END

echo 'checkmultisig' | ${BSST} --z3-enabled=true --is-incomplete-script=true --produce-model-values-for='*' --max-samples-for-dynamic-stack-access=2 --sigversion=base --log-progress=false | grep -v '        wit. :' >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

When wit1 = 0 as num_signatures :: [CHECKMULTISIG @ 1:L1]
---------------------------------------------------------

When wit1 = 1 as num_signatures :: [CHECKMULTISIG @ 1:L1]
---------------------------------------------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

When wit1 = 0 as num_signatures :: [CHECKMULTISIG @ 1:L1]
---------------------------------------------------------
Witnesses used: 3

Model values:

Stack values:
        stack[-1] = CHECKMULTISIG(1, wit0, wit1) = 1

When wit1 = 1 as num_signatures :: [CHECKMULTISIG @ 1:L1]
---------------------------------------------------------
Witnesses used: 4

Model values:
        wit1 = 1

Stack values:
        stack[-1] = CHECKMULTISIG(1, wit0, wit1, wit2) : 0

END

echo '1 checkmultisig' | ${BSST} --z3-enabled=true --is-incomplete-script=true --produce-model-values-for='*' --max-samples-for-dynamic-stack-access=2 --sigversion=base --log-progress=false | grep -v '        wit. :' >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

When \$a = x('0000') :: [PICK @ 1:L2]
------------------------------------

When \$a = x('0100') :: [PICK @ 1:L2]
------------------------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

When \$a = x('0000') :: [PICK @ 1:L2]
------------------------------------
Witnesses used: 1

Model values:
        wit0 : ?
        \$a = 0 <encoded: x('0000')>

Stack values:
        stack[-1] = wit0 : ...
        stack[-2] = wit0 : ...

When \$a = x('0100') :: [PICK @ 1:L2]
------------------------------------
Witnesses used: 2

Model values:
        wit0 : ?
        wit1 : ?
        \$a = 1 <encoded: x('0100')>

Stack values:
        stack[-1] = wit1 : ...
        stack[-2] = wit0 : ...
        stack[-3] = wit1 : ...

END

cat >${TESTIN} <<END
// bsst-assume(\$a): 0x0000 0x0100
\$a pick
END

cat ${TESTIN} | ${BSST} --z3-enabled=true --is-incomplete-script=true --produce-model-values-for='*' --log-progress=false --minimaldata-flag=false >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo "DYNAMIC STACK ACCESS TEST SUCCESS"
