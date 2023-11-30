#!/bin/sh

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
==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        <*> BOOL(EXAMPLE(10)) @ END

===================================================
Witness usage and model values for all valid paths:
===================================================
Witnesses used: 0

Model values:
	<result> = EXAMPLE(10) = 52

END

echo "10 EXAMPLE" | $BSST --plugins=plugins/op_example_bsst_plugin.py --z3-enabled=true > ${TESTOUT}

[ "x$(tail -n 17 ${TESTOUT})" == "x$(cat ${TESTEXPECTED})" ]

echo "010299" > ${TESTIN}
cat ${TESTIN} | ${BSST} --plugins=plugins/raw_input_bsst_plugin.py --is-elements=true > ${TESTOUT}

cat >${TESTEXPECTED} <<END

===============
Decoded script:
===============
x('02')                              // offset: 0 (0x0)
OP_RSHIFT                            // offset: 2 (0x2)
===============
END

[ "x$(head -n 7 ${TESTOUT})" == "x$(cat ${TESTEXPECTED})" ]

${BSST} --plugins=plugins/raw_input_bsst_plugin.py --is-elements=true --input-file=${TESTIN} > ${TESTOUT}

[ "x$(head -n 7 ${TESTOUT})" == "x$(cat ${TESTEXPECTED})" ]

printf "\x01\x02\x99" > ${TESTIN}

cat $TESTIN | ${BSST} --plugins=plugins/raw_input_bsst_plugin.py --is-elements=true --plugin-raw-input=binary > ${TESTOUT}

[ "x$(head -n 7 ${TESTOUT})" == "x$(cat ${TESTEXPECTED})" ]

${BSST} --plugins=plugins/raw_input_bsst_plugin.py --is-elements=true --plugin-raw-input=binary --input-file=${TESTIN} > ${TESTOUT}

[ "x$(head -n 7 ${TESTOUT})" == "x$(cat ${TESTEXPECTED})" ]

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

IF wit0 @ 1:L1 : True
---------------------

IF wit0 @ 1:L1 : False
----------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        EQUAL(0, SUB(wit0, CHECKSIG(\$a, \$b))) @ END

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 1

==================
Warnings per path:
==================

IF wit0 @ 1:L1 : False
----------------------
	warn_possible_success_without_sig_check @ END

END

echo 'dup if endif $a $b checksig sub 0 equal' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

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

        CHECKSIG(\$a, \$b) @ 4:L1
        <*> 1 @ END

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 0

END

echo '1 $a $b checksig verify' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo '1 $a $b nop checksigverify' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo '1 $a $b checksig drop' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

grep 'warn_possible_success_without_sig_check' ${TESTOUT}


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

        CHECKMULTISIG(2, \$c, \$b, 1, \$a) @ 8:L1
        <*> 1 @ END

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 0

END

echo '1 0 $a 1 $b $c 2 checkmultisig verify' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false  --sigversion=witness_v0 --log-progress=false > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo '1 0 $a 1 $b $c 2 nop checkmultisigverify' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false  --sigversion=witness_v0 --log-progress=false > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo '1 0 $a 1 $b $c 2 checkmultisig drop' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false  --sigversion=witness_v0 --log-progress=false > ${TESTOUT}

grep 'warn_possible_success_without_sig_check' ${TESTOUT}

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

        EQUAL(ADD(\$b, 1), CHECKSIGADD(\$a, \$b, \$c)) @ 8:L1
        <*> 1 @ END

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 0

END

echo '1 $a $b $c checksigadd $b 1 add equalverify' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo '1 $a $b $c checksigadd $b 0 add equalverify' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

grep 'warn_possible_success_without_sig_check' ${TESTOUT}

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

        GREATERTHANOREQUAL(CHECKSIGADD(\$c, CHECKSIGADD(\$a, 0, \$b), \$d), 1) @ END

==============
Unused values:
==============

	CHECKSIGADD(\$e, CHECKSIGADD(\$c, CHECKSIGADD(\$a, 0, \$b), \$d), \$f) from 13:L1

==================================
Witness usage for all valid paths:
==================================
Witnesses used: 0

END

echo '$a 0 $b checksigadd $c swap $d checksigadd dup toaltstack $e swap $f checksigadd drop fromaltstack 1 greaterthanorequal' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo '$a 0 $b checksigadd $c swap $d checksigadd dup toaltstack $e swap $f checksigadd drop fromaltstack 0 greaterthanorequal' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

grep 'warn_possible_success_without_sig_check' ${TESTOUT}

echo "PLUGINS TEST SUCCESS"

