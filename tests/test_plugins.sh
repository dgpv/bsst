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

        <*> BOOL(EXAMPLE(10)) @ END

===============================
Witness usage and model values:
===============================

All valid paths:
----------------
Witnesses used: 0

Stack values:
        <result> = EXAMPLE(10) = 52

END

echo "10 EXAMPLE" | $BSST --plugins=plugins/op_example_bsst_plugin.py --z3-enabled=true --log-progress=false > ${TESTOUT}

# [ "x$(tail -n 17 ${TESTOUT})" == "x$(cat ${TESTEXPECTED})" ]
diff -u ${TESTOUT} ${TESTEXPECTED}

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

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 1

Stack values:
        <result> = EQUAL(0, SUB(wit0, CHECKSIG(\$a, \$b))) : one_of(0, 1)

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

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 0

Stack values:
        <result> = 1

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

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 0

Stack values:
        <result> = 1

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

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 0

Stack values:
        <result> = 1

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

=================================
Witness usage and stack contents:
=================================

All valid paths:
----------------
Witnesses used: 0

Stack values:
        <result> = GREATERTHANOREQUAL(CHECKSIGADD(\$c, CHECKSIGADD(\$a, 0, \$b), \$d), 1) : one_of(0, 1)

END

echo '$a 0 $b checksigadd $c swap $d checksigadd dup toaltstack $e swap $f checksigadd drop fromaltstack 1 greaterthanorequal' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo '$a 0 $b checksigadd $c swap $d checksigadd dup toaltstack $e swap $f checksigadd drop fromaltstack 0 greaterthanorequal' | ${BSST} --plugins=plugins/checksig_track_bsst_plugin.py --z3-enabled=true --is-elements=true --use-parallel-solving=false --produce-model-values=false --log-progress=false > ${TESTOUT}

grep 'warn_possible_success_without_sig_check' ${TESTOUT}

cat >${TESTEXPECTED} <<END

============
Valid paths:
============

IF \$a @ 33:L25 : True
---------------------

IF \$a @ 33:L25 : False
----------------------

==============================
Enforced constraints per path:
==============================

All valid paths:
----------------

        CHECKMULTISIG(2, x('02').\$w0, \$w1, 2, x('30').\$w2, \$w3) @ 25:L19
        CHECKSIGFROMSTACK(\$w6, \$w5, \$w4) @ 27:L21
        <*> EQUAL(\$w5, 0) @ END

IF \$a @ 33:L25 : True
---------------------

        CHECKSIGFROMSTACK(\$w7, x('11').SHA256(\$w5), \$w4) @ 42:L28
        {*} BOOL(ADD(0, CHECKSIGFROMSTACK(\$w7, x('11').SHA256(\$w5), \$w4))) @ 45:L28

IF \$a @ 33:L25 : False
----------------------

        CHECKSIGFROMSTACK(\$w7, x('22').SHA256(SHA256(\$w5)), \$w4) @ 42:L28
        {*} BOOL(ADD(0, CHECKSIGFROMSTACK(\$w7, x('22').SHA256(SHA256(\$w5)), \$w4))) @ 45:L28

===============================
Witness usage and model values:
===============================

All valid paths:
----------------
Witnesses used: 0

Model values:
        \$w7 = x('300a0203637d7e0203170f18')
        # Size = 12
        # Used as signature in CHECKSIGFROMSTACK @ 42:L28 (in enforcements @ 42:L28, 45:L28)

        \$w6 = x('300702016d02022cc2')
        # Size = 9
        # Used as signature in CHECKSIGFROMSTACKVERIFY @ 27:L21 (in enforcement @ 27:L21)

        \$w5 : x('')
        # Size = 0
        # Used in enforcement @ END
        # Used as data in CHECKSIGFROMSTACKVERIFY @ 27:L21 (in enforcement @ 27:L21)
        # Used as dependency of data in CHECKSIGFROMSTACK @ 42:L28 (in enforcements @ 42:L28, 45:L28)
        # Used as preimage in SHA256 @ 31:L24 (in enforcements @ 42:L28, 45:L28)

        \$w4 = x('02d3315c8fb1dd88b5dd0002040684094f505152535455565758595a5b5c5d5e5f')
        # Size = 33
        # Used as pubkey in CHECKSIGFROMSTACKVERIFY @ 27:L21 (in enforcement @ 27:L21)
        # Used as pubkey in CHECKSIGFROMSTACK @ 42:L28 (in enforcements @ 42:L28, 45:L28)

        \$w3 = x('3008020100020374a76e81')
        # Size = 11
        # Used as signature in CHECKMULTISIGVERIFY @ 25:L19 (in enforcement @ 25:L19)

        \$w2 = x('0602017902012f81')
        # Size = 8
        # Used as dependency of signature in CHECKMULTISIGVERIFY @ 25:L19 (in enforcement @ 25:L19)

        \$w1 = x('03f2325e8db3df89b6de0103050785f7f8f9fafbfcfdfeff000102030405060708')
        # Size = 33
        # Used as pubkey in CHECKMULTISIGVERIFY @ 25:L19 (in enforcement @ 25:L19)

        \$w0 = x('d3315c8fb1dd88b5dd0002040684094f505152535455565758595a5b5c5d5e5f')
        # Size = 32
        # Used as dependency of pubkey in CHECKMULTISIGVERIFY @ 25:L19 (in enforcement @ 25:L19)

IF \$a @ 33:L25 : False
----------------------
Witnesses used: 0

Model values:
        \$w5 : ...
        # Used as dependency of preimage in SHA256 @ 36:L25 (in enforcements @ 42:L28, 45:L28)

END

cat >${TESTIN} <<END
// bsst-assume(\$w0): 0xd3315c8fb1dd88b5dd0002040684094f505152535455565758595a5b5c5d5e5f
// bsst-assume(\$w1): 0x03f2325e8db3df89b6de0103050785f7f8f9fafbfcfdfeff000102030405060708
// bsst-assume(\$w2): 0x0602017902012f81
// bsst-assume(\$w3): 0x3008020100020374a76e81
// bsst-assume(\$w4): 0x02d3315c8fb1dd88b5dd0002040684094f505152535455565758595a5b5c5d5e5f
// bsst-assume(\$w5): ''
// bsst-assume(\$w6): 0x300702016d02022cc2
// bsst-assume(\$w7): 0x300a0203637d7e0203170f18

\$w7 \$w6 \$w5 \$w4 \$w3 \$w2 \$w1 \$w0

0x02 SWAP CAT
TOALTSTACK TOALTSTACK
0x30 SWAP CAT
TOALTSTACK TOALTSTACK
0
FROMALTSTACK FROMALTSTACK 2
FROMALTSTACK FROMALTSTACK 2
CHECKMULTISIGVERIFY
3DUP
CHECKSIGFROMSTACKVERIFY
ROT DROP
SWAP
SHA256
\$a IF 0x11 ELSE SHA256 0x22 ENDIF
SWAP CAT
SWAP
CHECKSIGFROMSTACK 0 ADD VERIFY
\$w5 0 EQUAL
END

cat ${TESTIN} | ${BSST} --is-elements=true --z3-enabled=true --produce-model-values-for='$w?' --report-model-value-sizes=true --plugins=plugins/model_value_usage_track_bsst_plugin.py --sigversion=witness_v0 --log-progress=false > ${TESTOUT}

diff -u ${TESTOUT} ${TESTEXPECTED}

echo "PLUGINS TEST SUCCESS"

