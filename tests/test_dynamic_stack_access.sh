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

PICK wit0 @ 0:L1 : 0
--------------------

PICK wit0 @ 0:L1 : 1
--------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

PICK wit0 @ 0:L1 : 0
--------------------
Witnesses used: 2

Model values:
        wit0 : 0
        wit1 : ?

Stack values:
        stack[-1] = wit1 : ...
        stack[-2] = wit1 : ...

PICK wit0 @ 0:L1 : 1
--------------------
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

PICK wit0 @ 0:L1 : 2, ...
-------------------------
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

ROLL wit0 @ 0:L1 : 0
--------------------

ROLL wit0 @ 0:L1 : 1
--------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

ROLL wit0 @ 0:L1 : 0
--------------------
Witnesses used: 2

Model values:
        wit0 : 0
        wit1 : ?

Stack values:
        stack[-1] = wit1 : ...

ROLL wit0 @ 0:L1 : 1
--------------------
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

ROLL wit0 @ 0:L1 : 2, ...
-------------------------
The path was not explored

END

echo 'roll' | ${BSST} --z3-enabled=true --is-incomplete-script=true --max-samples-for-dynamic-stack-access=2 --log-progress=false >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

PICK &a @ 5:L3 : 1
------------------

PICK &a @ 5:L3 : 2
------------------

PICK &a @ 5:L3 : 3
------------------

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

PICK wit0 @ 5:L3 : 1
--------------------
Witnesses used: 3

Model values:
        wit0 = &a = 1
        wit1 : ?
        wit2 : ?

Stack values:
        stack[-1] = wit2 : ...
        stack[-2] = wit1 : ...
        stack[-3] = wit2 : ...

PICK wit0 @ 5:L3 : 2
--------------------
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

PICK wit0 @ 5:L3 : 3
--------------------
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

ROLL &a @ 5:L3 : 1
------------------

ROLL &a @ 5:L3 : 2
------------------

ROLL &a @ 5:L3 : 3
------------------

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

ROLL wit0 @ 5:L3 : 1
--------------------
Witnesses used: 3

Model values:
        wit0 = &a = 1
        wit1 : ?
        wit2 : ?

Stack values:
        stack[-1] = wit2 : ...
        stack[-2] = wit1 : ...

ROLL wit0 @ 5:L3 : 2
--------------------
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

ROLL wit0 @ 5:L3 : 3
--------------------
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

CHECKMULTISIG @ 0:L1 : num_keys = 0
-----------------------------------

CHECKMULTISIG @ 0:L1 : num_keys = 1
CHECKMULTISIG @ 0:L1 : num_signatures = 0
-----------------------------------------

CHECKMULTISIG @ 0:L1 : num_keys = 1
CHECKMULTISIG @ 0:L1 : num_signatures = 1
-----------------------------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

CHECKMULTISIG @ 0:L1 : num_keys = 0
-----------------------------------
Witnesses used: 3

Model values:

Stack values:
        stack[-1] = CHECKMULTISIG(wit0, wit1) = 1

CHECKMULTISIG @ 0:L1 : num_keys = 1
-----------------------------------

Model values:
        wit0 = 1

CHECKMULTISIG @ 0:L1 : num_keys = 1
CHECKMULTISIG @ 0:L1 : num_signatures = 0
-----------------------------------------
Witnesses used: 4

Model values:

Stack values:
        stack[-1] = CHECKMULTISIG(wit0, wit1, wit2) = 1

CHECKMULTISIG @ 0:L1 : num_keys = 1
CHECKMULTISIG @ 0:L1 : num_signatures = 1
-----------------------------------------
Witnesses used: 5

Model values:
        wit2 = 1

Stack values:
        stack[-1] = CHECKMULTISIG(wit0, wit1, wit2, wit3) : 0

==================
Failures per path:
==================

CHECKMULTISIG @ 0:L1 : num_keys : 2, ...
----------------------------------------
The path was not explored

END

echo 'checkmultisig' | ${BSST} --z3-enabled=true --is-incomplete-script=true --produce-model-values-for='*' --max-samples-for-dynamic-stack-access=2 --sigversion=base --log-progress=false | grep -v '        wit. :' >${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

CHECKMULTISIG @ 1:L1 : num_signatures = 0
-----------------------------------------

CHECKMULTISIG @ 1:L1 : num_signatures = 1
-----------------------------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

CHECKMULTISIG @ 1:L1 : num_signatures = 0
-----------------------------------------
Witnesses used: 3

Model values:

Stack values:
        stack[-1] = CHECKMULTISIG(1, wit0, wit1) = 1

CHECKMULTISIG @ 1:L1 : num_signatures = 1
-----------------------------------------
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

PICK \$a @ 1:L2 : x('0000')
--------------------------

PICK \$a @ 1:L2 : x('0100')
--------------------------

=======================
No enforced constraints
=======================

===============================
Witness usage and model values:
===============================

PICK \$a @ 1:L2 : x('0000')
--------------------------
Witnesses used: 1

Model values:
        wit0 : ?
        \$a = 0 <encoded: x('0000')>

Stack values:
        stack[-1] = wit0 : ...
        stack[-2] = wit0 : ...

PICK \$a @ 1:L2 : x('0100')
--------------------------
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
