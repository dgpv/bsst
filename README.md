
# B'SST: Bitcoin-like Script Symbolic Tracer

Copyright (c) 2023 Dmitry Petukhov (https://github.com/dgpv), dp@bsst.dev

Symbolically executes the opcodes, tracks constraints that opcodes impose on
values they operate on, and shows the report with conditions that the script
enforces, possible failures, possible values for data, etc.

Supports Bitcoin script and Elements script.

**IMPORTANT**: This program can help uncover problems with the scripts it analyses,
BUT it cannot guarantee that there are no problems, inconsistenses, bugs,
vulnerabilities, et cetera in the analyzed script. This program itself or the
underlying libraries can also contain bugs or other inconsistencies that could
preclude detection of the problems with the analyzed script. For some type
of problems, the analysis algorithm just cannot detect them at all.

This program should be used as an additional layer of defence in the struggle
to detect defects and unexpected behavior in the scripts, much like other
things like testing or code audit are used for this purpose, simply reducing
the probability of defects being undetected. It can also be used as a tool to
better understand the behavior of analyzed scripts.

[Elements script interpreter](https://github.com/ElementsProject/elements/blob/master/src/script/interpreter.cpp),
which is an extension of Bitcoin script interpreter, was used as reference.
Efforts have been made to match the behavior of reference interpreter closely, but it
will obviously never be a 100%, consensus-correct, match.

## License

Free for non-commercial use. Licensed under Prosperity Public License 3.0.0.
This license allows for thirty-day trial period for commercial purposes. There are also
exemptions for educational institutions, public research organizations, etc.
Please read LICENSE.md for the full text of the license.
For inquiries, please write to license@bsst.dev

Contains portions of the code that were originally released under MIT software
license. These are code of the CSHA256 class (derived from MIT-licensed code,
that was authored by various Bitcoin Core developers) and ripemd160 function
(MIT-licensed code, authored by Pieter Wuille). Please refer to the source code
of bsst python module for more information on these.

## Thoroughness vs speed of analysis

It is highly recommended to have [Z3 theorem prover](https://github.com/Z3Prover/z3) python
package installed (see Optional Dependencies below), and run `bsst-cli` with `--z3-enabled=true`
setting. Without this, a lot of possible issues decectable with help of Z3 will not be detected.

Still, running with `--z3-enabled=false` (the default setting) can be useful in some contexts,
where speed of checking is more important than thoroughness.

## Dependencies

Python 3.10 or later is required

## Optional Dependencies

For B'SST to be able to use Z3 theorem prover, "z3-solver" python package
(https://pypi.org/project/z3-solver/) is needed.

For the analyzer to check validity of statically-known public keys,
secp256k1 C library (https://github.com/bitcoin-core/secp256k1/) is needed.
B'SST will attempt to find it with `ctypes.util.find_library` and then load it
using `ctypes.cdll.LoadLibrary`.

## Syntax

Syntax parser is rather basic:

* Case-insensitive
* `OP_ADD` is the same as `ADD`,
* The string `'data'` can be represented as: `'data'`, `x('64617461')`, or `0x64617461`. Only single quotes are recognized for strings.
* Strings in quotes cannot contain whitespace, single quotes, or comment markers. If you need whitespace, single quote, or comment marker in the string, use hex encoding.
* LE64 value 555 can be represented as `x('2b02000000000000')`, `0x2b02000000000000`, or `le64(555)`.
* ScriptNum values are represented with normal base10 integers.
* Data (but not opcodes) can be enclosed in angle brackets (like this: `<0x1234>`), and these angle brackets will be ignored (for compatibilty with ScriptWiz IDE syntax)

`//` marks the start of the comment, that spans to end of line. This character sequence can be changed with `--comment-marker` setting. Note that comments are removed before parsing the rest of the line, and because of this, comment markers cannot appear within quoted strings

### Data placeholders

Identifiers starting with `$` are recognized as data placeholders: `$some_var`

### Data references

A special format of comment is recoginzed:

`OP_ADD // =>add_result` will mark the value on the stack after `OP_ADD` with
the identifier `add_result`, and this reference will be used in the report.
There should be no whitespace between `=>` and the reference identifier. There may be
whitespace between `//` and `=>`, but nothing other than whitespace. In the case when
different code paths result in different values assigned to the same reference identifier,
an apostrophe <<'>> will be appended to the identifier with different value.

The data reference identifiers will be prepended with `&` in the report

### Assertions

Specially-formatted comments can be used to put constraints on value on top of the stack: `// bsst-assert:` and `// bsst-assert-size:`. The difference is that the former puts constraints on the value itself, while the latter constraints the
data size instead of value.

The expressibility of these assertions are limited, as their primary purpose is to help the solver by reducing the range of values to be considered.

For the value on top of the stack constrained via assertion, B'SST will check
if the value can happen to be outside the range defined by the assertion
expression. If it can, the currently analyzed execution path will be deemed
as failed, and in the report the failure will be shown as
`assertion failed at line <N>` or `check_assertion_at_line_<N>` where `<N>`
would be the line at which the failing `// bsst-assert:` comment is at.

After the assertion check is successfully passed, the value will be assumed to be
constrained by the assertion expression.

The difference between `assertion failed at line <N>` and `check_assertion_at_line_<N>` is that the former is detected at the time the assertion is applied at the
position in the script it resides on, while the later is detected afterwards, when other constraints are imposed on values, and that may cause the assertion constraints to be violated.

A data reference can be supplied as argument, like `// bsst-assert(&ref):` or `// bsst-assert-size(&ref):`, and then the target of the assertion will be this data reference instead of the top of the stack. The assertion will be checked at the place where the assetion itself is declared, not at the place where the data reference is declared.

A witness name in the form of `wit<N>` where `<N>` is a number, is also accepted as assertion argument. The witness must be referenced by the script at the time when assertion is checked, otherwise the assertion will be ignored (with a warning)

#### Assertion expression syntax

After `:`, a whitespace-separated list of expressions is expected,
finished at end of line. The following is recognized in expressions:

- decimal number: scriptnum equal to the number, for example `1`, `-33`
- le64(<number>): LE64 value equal to the number, for example `le64(0)`, `le64(125)`
- bytes in hex (either as 0x1234 or x('1234'): bytes equal to the hex-encoded
- string in single quotes: bytes equal to utf-8 encoding of the string

Before these, `!=` can be placed to express non-equality. `=` can also be placed
before these, for readability: `=42` is the same as `42`. `!=le64(0)` means
"not equal to 64-byte zero", `!='abc'` means "not equal to the string 'abc'"

Before decimal number or le64 number, `>`, `<`, `>=`, `<=` can be placed
to express "greater than", "less than", "greater or equal", "less or equal",
for example `>0`, `<=-44`, `>=le64(999)`

For decimal or le64 numbers, a range expression is recognized: `1..456` means
from 1 to 456. Likewise, `le64(1)..le64(456)`

Within one `// bsst-assert:` or `// bsst-assert-size:`, space-separated
expressions are combined with `OR` logic.
For example, `OP_ADD // bsst-assert: >1 !=8 <=-3` would express
that "result of `OP_ADD` must be above 1 or not equal to 8 or less than or equal
to -3". Note that !=8 here is meaningless, because (`>1` OR `!=8`) is the same
as `>1`. So this expression constraints the value to "any representable
scriptnum, except -2, -1, 0, 1"

If more than one `// bsst-assert:` or `bsst-assert-size:` is placed without any
script opcode or data between them, the expressions of the asserts since
last opcode or data will be combined with `AND` logic. For example,

```
OP_ADD // bsst-assert: >1 <=-3 -44..55
       // bsst-assert: 'a'
       // bsst-assert-size: 1
```

Will express

```
((value above 1) OR (value below -2) OR (value between -44 and 55 inclusive))
AND (value equal to 'a')
AND (data size equal 1)
```

Note that expressions other than "value equal to 'a'" here are meaningless, but included for illustration purposes.

Integers in asserts also impose scriptnum-encoding constraints on their targets.
That is, `// bsst-assert: 3 0x00` is the same as `// bsst-assert: 3`, unless
`---minimaldata-flag=false`, because `0x00` is not a minimal-encoded scriptnum,
and, given that values are combined with `OR` logic, it will just be ignored.

Combining `3` and `0x00` with two separate asserts on the same target value with
the same minimaldata flag setting will result in assertion to always be triggered,
because then these two will be combined with `AND` logic, and the result will be
an empty set

Asserts with LE64 integers also impose a constraint of 'size is exactly 8 bytes'
on their targets.

Mixing scriptnum and LE64 values in assert on the same target value is not
allowed, although mixing scriptnums with arbitrary byte expressions is allowed.

### Assumptions

Specially-formatted comments can be used to put unconditional constraints
on data placeholders: `// bsst-assume($name):` and `// bsst-assume-size($name):`
to apply assumption to the data  placeholder `$name`.

Assumptions differ from assertions in the following:

- Only work with data placeholders
- Applied to corresponding data placeholder regardless of where the assumption or the data placeholder reside in the source file
- No check is performed to determine if the value can be outside of the range defined by the expression. The constraints defined by the expression are simply assumed to apply to the corresponding data placeholder

In other aspects, assumptions work similar to assertions. The syntax for expressions is the same, different assumptions with the same data placeholder are combined with `AND` logic, `// bsst-assume-size($name):` works with data size instead of value, etc.

Note that if conflicting assumptions are placed on a data placeholder,
or an assumed constraint on data placeholder might possibly relate to a script
failure, you can still see error code `check_assumption_at_line_<N>` where `<N>`
points to the line with an assumption

## Reports

The reports show:

* Valid paths: execution paths (branches with branch condition values) that can result in successful script completion
* Enforced constraints: per-path list of constraints that must be satisfied for the successful script completion.
  If constraint is identical in all sub-paths, it will be moved up one level of path hierarchy.

    - If constraint condition is always true, it will be marked with `<*>`
    - If constraint condition is always true in particular execution path, it will be marked with `{*}`
      (unless `--mark-path-local-always-true-enforcements` is set to `false`)
    - If constraint condition is shown as `BOOL(<condition>)`, that means the condition is passed to `CastToBool()`:
      empty data, arbitrary-length block of zero bytes, as well as arbitrary-length 'negative zero' (zero-bytes block
      ended with byte 0x80) are seen as `false`, while any other value is seen as `true`. If it is obvious that the
      condition is already boolean (like the result of `LESSTHAN`, for example), the condition is not shown wrapped in `BOOL`.

* Model values: possible values for various variables such as witnesses, script result, or transaction fields
  (in Elements mode, where there are transaction introspection opcodes)

    - If there could be more values, the name and the value will be separated with `:`
    - If it is found that only one value is possible, the name and the value will be separated with `=`
    - If the value is totally unknown, it will be `?`

* Warnings: possible issues dected while symbolically executing the script, that do not lead to script failure,
  but it is probably better to examine them and understand if they are problematic or not
* Failures: Information on detected script failures, with opcode that might have caused the vailure, and stack contents
  at the moment this opcode would be executed
* Progress log: if `--log-progress` is `true`, the details of checking of 'always true' conditions for enforced constraints,
  and 'only one possible value' for model values will be reported - namely, the 'probable cause' of why the condition is
  deemed always true or only one possible value is found, will be printed.

Some opcodes are abbreviated: `CHECKLOCKTIMEVERIFY` -> `CLTV`, `CHECKSEQUENCEVERIFY` -> `CSV`.
For Elements mode, `'a' 'b' CAT` will be reported as `'a'.'b'`

NOTE: Model values are described as "possible" values in a sense that they satisfy restrictions imposed on them by opcodes,
as modelled by B'SST. Since modelling is not perfect, sometimes incomplete, these values can still be invalid if used
for execution of the script on "real" interpreter. For example, for ECDSA pubkeys only constraints on size and
first byte are modelled, and model value can show arbitrary data for the rest of pubkey.

NOTE: With Z3 enabled, failure report may give several possible causes for the failure. It does not mean that
all of these conditions are a definite cause of this particular failure. Some of them may be false positives,
but this is the nature of Z3 - it gives 'possible causes' for constraint violation, and for the report to give
more concrete place of failure, much more constraints would need to be placed by the code, which can significantly
slow down the solving times, and there's still no guarantees that you would always get just one definitive cause of
constraint violation.

NOTE: If one enforcement condition is always true because of the other enforcement condition, and vise versa,
they will likely be both marked with `<*>`, For example, for `DUP 1 EQUALVERIFY 1 ADD 2 EQUAL` both enforcements
will be marked with `<*>` (with Z3 enabled). That does not mean that both checks are redundant. Only some of the
interlocked checks might happen to be be redundant. You always need to reason about the script logic to understand
why certain checks are marked with `<*>` and if it is wise to remove checks that seem to be redundant.

### Example report

For this rather complex Elements script:

https://github.com/fuji-money/tapscripts/blob/with-annotations-for-bsst/beta/mint-mint.tapscript

B'SST gives this report:

https://gist.github.com/dgpv/b57ecf4d9e3d0bfdcc2eb9147c9b9abf

## Custom opcodes

Please look at `examples/example_op_plugin.py`. With `--op-plugins=examples/example_op_plugin.py`,
B'SST will recognize `EXAMPLE` custom opcode.

## Assumptions and omissions

B'SST makes certain assumptions, and omits modelling some of the aspects of the script.

Below is (probably incomplete) list of these assumptions and omissions:

`CODESEPARATOR` is not modelled, and treated as NOP

`OP_SUCCESS` and "upgradeable NOPs" are not modelled

For non-tapscript modes, Script size limit is not modelled, but the 'number of opcodes' limit is modelled

The following script flags are assumed to be always set (consensus-enforced at the time of writing, mid-2023):

`SCRIPT_VERIFY_DERSIG`, `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY`, `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY`
for all modes, and `SCRIPT_SIGHASH_RANGEPROOF` for Elements mode

The following script flags are not modelled, because modelling them is practically infeasible,
only relevant for things outside of script execution itself, or only apply to non-modelled parts
of the script: `SCRIPT_VERIFY_SIGPUSHONLY`, `SCRIPT_VERIFY_CONST_SCRIPTCODE`,
`SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_TAPROOT_VERSION`, `SCRIPT_VERIFY_DISCOURAGE_OP_SUCCESS`,
`SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS`, `SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM`,
`SCRIPT_VERIFY_P2SH`, `SCRIPT_VERIFY_WITNESS`, `SCRIPT_VERIFY_TAPROOT` for all modes,
and `SCRIPT_NO_SIGHASH_BYTE` for Elements mode.

For `SCRIPT_VERIFY_LOW_S`, signatures are checked for "Low S" condition only if their data is known statically

Script size limit is not modelled (the limit of 10000 bytes that exists for segwit and pre-segwit)

## No API except command line

Currently, the only supported API is the command line.

While it is possible to import `bsst` module in python and call functions
from it, anything inside `bsst` module should be considered arbitrary and subject to change without
notice.

The command line interface may also change, but the changes will be noted in [Release notes](release-notes.md)

## Interrupting the solver

When the solver is working, it can be interrupted by sening it a SIGINT signal (usually done with `^C` on the terminal). After interruption, the solver will retry an attempt at solving (with different random seeds, unless solver randomization is disabled), for the maximum amount of tries set with `--max-solver-tries`. To cancel the analysis altogether and quit the program while the solver works, you will need to send a signal other than SIGINT to the program, for example SIGQUIT (usually done with `^\` on the terminal)

## Installation

Simply clone the repo:

`git clone https://github.com/dgpv/bsst/`

`cd bsst`

`./bsst-cli --help`

The file `bsst/__init__.py` is itself a runnable script without any mandatory dependencies except python standard library.
It is possible to just copy `bsst/__init__.py` into a convenient location under convenient name, and run it directly,
without installing `bsst` python module.

## Usage:

        bsst-cli [options] [settings]

## Available options:

  --help

        Show help on usage

  --license

        Show the software license this program is released under

  --version

        Show version

## Available settings:

  Default value for each setting is shown after the '=' sign

  --input-file='-'

        The file of the script to analyze. The dash "-" means STDIN

  --z3-enabled=false

        If true, Z3 theorem prover (https://github.com/Z3Prover/z3)
        will be employed to track and enforce constraints on values processed
        by the script. This will significantly improve the thoroughness of
        the analysis.
        If false, the analysis will be fast, but not as thorough, much fewer
        issues may be detected

  --z3-debug=false

        Enabling this will set `--all-z3-assertions-are-tracked-assertions`
        to true, and also shows all triggered tracked assertions as possible
        script failures

  --comment-marker='//'

        A marker that designates the start of the comment. The comment
        spans to the end of line. Comments are removed before any parsing is
        done on the source, and therefore the comment marker cannot appear
        within quoted strings. Any non-whitespace sequence of non-alphanumeric
        characters is allowed as a comment marker. Using characters that appear
        in your source in non-comment sections might lead to confusion, so
        please use this setting with caution

  --points-of-interest=''

        A set of "points" in the script to report the execution state at,
        in addition to the usual information in the report.
        The "point" can be an integer - that means the program counter position
        in the script, or the string "L<num>" where "<num>" is the line number
        in the text of the script

  --explicitly-enabled-opcodes=''

        A set of opcodes to explicitly enable

  --produce-model-values=true

        Produce 'model values' for fields of transaction, witnesses, and
        the value(s) on the stack after execution has finished (if
        `--is-incomplete-script` is true or `--cleanstack-flag` is false,
        there may be more than one value on the stack at the end of successful
        execution).
        
        Model values are the values that, when assigned to said fields, do not
        lead to the script failure. If there is only one such possible value,
        it will be shown with '=' between the name and the value in the report,
        otherwise the separator will be ':'.

  --check-always-true-enforcements=true

        Use Z3 to check enforcements for being 'always true': that is,
        the enforcement condition being false means that no valid execution
        paths exist in the script. Turning this setting off skips that
        detection, which means that the analysis will finish faster.

        When condition is detected as 'always true' it will be marked with
        "<*>" in the report. Always-true conditions may indicate either an
        issue with the script (like, doing `$data DUP EQUALVERIFY` instead of
        `DUP $data EQUALVERIFY`), or an opportunity for optimization, if after
        further analysis it is obvious that other conditions make this
        'always true' enforcement unnecessary. Sometimes the enforcement is
        'always true' only in particular execution path (see
        `--mark-path-local-always-true-enforcements`).

        Sometimes 'always true' condition for enforcements can also be detected
        without use of Z3, this settings will not affect these cases.

  --log-progress=true

        Print progress log as the script is analyzed.
        The progress log lines are sent to STDOUT

  --log-solving-attempts=true

        In addition to progress log, log info about each solving attempt

  --log-solving-attempts-to-stderr=false

        In addition to progress log, log info about each solving attempt
        to STDERR

  --all-z3-assertions-are-tracked-assertions=false

        Set names for all Z3 assertions generated, making them "tracked".
        This will severely slow down the solving speed. But it may sometimes
        help to find more about the probable cause for 'always true'
        enforcement or for 'only one possible model value'. Automatically
        set to true if `--z3-debug` is true

  --use-parallel-solving=true

        Enable running several solvers in parallel.
        if `--parallel-solving-num-processes` is not set, then the number
        of CPUs on the machine will be used. Using parallel solvers is
        likely to speed up the solving. Will be automatically turned off
        if `--use-z3-incremental-mode` is true. Parallel solving is only
        available on the platforms that support 'fork' system call for
        'start method' of python multiprocessing module (that means that
        parallel solving is not supported on Windows or MacOS)

  --parallel-solving-num-processes=0

        Number of solver processes to run in parallel. If zero, then
        number of available CPU will be used

  --solver-timeout-seconds=5

        Timeout in seconds after which the Z3 solving attempt will be
        abandoned, and another attempt will start. Zero means no timeout.
        
        When solver randomization is enabled (`--disable-z3-randomization` is
        false), restarting solver can often help to find solution faster

  --solver-increasing-timeout-max=31536000

        Maximum value for solver timeout when increasing timeout is
        employed (via `--solver-increasing-timeout-multiplier`)

  --solver-increasing-timeout-multiplier=1.5

        Multiplier to increase the solver timeout after each attempt
        For example, if set to 1.5 and `--solver-timeout-seconds` is 10,
        on the second attempt the timeout will be 15 seconds, on third addempt
        22.5 seconds, etc.

  --max-solver-tries=100

        Maximum timer of tries for the solver to get sat or unsat result.
        After this number of tries, the analyzer will exit if
        `--exit-on-solver-result-unknown` is true, or will continue analysis.
        In the later case, the analysis might not be correct, because the
        assertions of the unsolved case will be ignored

  --exit-on-solver-result-unknown=true

        If true, then when the solver did not produce sat or unsat after
        `--max-solver-tries` attempts, stop the analysis and exit

  --use-z3-incremental-mode=false

        Incremental mode will use weaker solvers (and the solver can run
        for a long time for certain scripts). Non-incremental mode resets the
        solver for each branch, and re-adds all constraints tracked from the
        start of the script, so it will re-check all the constraints for each
        branch. But because Z3 will use stronger solvers in non-incremental
        mode, solving times will likely to actually be faster than in
        incremental mode.  In incremental mode, the randomizations of z3 seeds
        or shuffling of assertions will not be performed, and no repeated
        attempts at finding solutions will be performed on 'unsat' from solver.
        Also no attempts to check if enforcements can be 'always true' will
        be peformed

  --disable-error-code-tracking-with-z3=false

        Disable error code tracking in Z3 assertions. Script failures
        will still be detected as with enabled error code tracking, but
        the failure will be reported as "untracked constraint check failed".
        Disabling error code tracking can speed up solving, at the price
        of losing information about concrete error codes

  --is-incomplete-script=false

        If true, final result check will be skipped, and
        `--cleanstack-flag` will be set to false

  --restrict-data-reference-names=true

        If false, named references to values in the script via
        specially-formatted comments will be unrestricted, except that
        apostrophe <<'>> is not allowed. Otherwise, these
        names will be checked to be valid python identifiers

  --assume-no-160bit-hash-collisions=false

        If true, it is assumed that 160-bit hashes will never collide,
        and the expression "For all x, y, hashfun(x) == hashfun(y) <=> x == y"
        can be deemed true. (NOTE: it is always assumed that 256-bit hash
        functions will never collide)

  --skip-immediately-failed-branches-on='VERIFY'

        A script fragment that is expected to fail if top of the stack
        is not True. Will be looked for right after opcodes that leave the
        'success' flag on the stack, like for example ADD64 or MUL64. Any
        enforcement inside that script fragment, that would otherwise be
        registered, will be ignored. Sequences like `ADD64 VERIFY` can
        be viewed as a single opcode that fails on invalid arguments.
        This setting allows the analysis to do just that. If for some reason
        the script uses different sequence of opcodes to detect such failures,
        like for example `1 EQUALVERIFY`, you can set this option with the
        string "1 EQUALVERIFY", or empty string to disable this mechanism.

  --is-miner=false

        If true, the analysis will assume that only consensus rules apply,
        and policy rules are not (as what would be the case when the script is
        executed by the miner). It is a good idea to analyze both with
        `--is-miner=true` and `--is-miner=false`, to see if the script behavior
        can be different for 'policy rules' vs 'consensus rules'

  --is-elements=false

        If true, Elements opcodes and rules will be enabled

  --sigversion=tapscript

        Rules for script execution. One of: base, witness_v0, tapscript

  --dont-use-tracked-assertions-for-error-codes=false

        If true, error code detection will use implication instead
        of tracked assertions

  --disable-z3-randomization=false

        Disable randomization for Z3 solver.
        Will likely make solving slower

  --do-progressive-z3-checks=true

        Perform Z3 check after each opcode is symbolically executed.
        When true, analysis time for the whole script will likely be longer,
        but some failures might be detected faster. Also might give
        clearer reasons for paricular failure when the failure is detected
        right after the opcode rather than at the end of execution path

  --tag-data-with-position=false

        If true, each value pushed on the stack will be tagged with
        the value of program counter at the time it was pushed. This will
        make the analysis treat such values as unique within each execution
        path, even if values might actually be the same

  --tag-enforcements-with-position=true

        If true, each enforcement will be tagged with the value of program
        counter at the time it was enforced by the secipt. This will make the
        analysis treat such enforcements as unique within each execution path,
        even if the enforced conditions might be the same

  --use-deterministic-arguments-order=true

        If true, the opcodes where the order of arguments is not important
        will have their arguments sorted according to their canonical
        representation. For example, ADD(3, 1) will be analysed and represented
        as ADD(1, 3)

  --mark-path-local-always-true-enforcements=true

        If true, the enforcements that are always true only in certain
        execution path, but not in all valid execution paths, will be
        marked with "{*}"

  --discourage-upgradeable-pubkey-type-flag=true

        SCRIPT_VERIFY_DISCOURAGE_UPGRADEABLE_PUBKEY_TYPE

  --strictenc-flag=true

        SCRIPT_VERIFY_STRICTENC

  --witness-pubkeytype-flag=true

        SCRIPT_VERIFY_WITNESS_PUBKEYTYPE

  --minimalif-flag=true

        SCRIPT_VERIFY_MINIMALIF

  --minimaldata-flag=true

        SCRIPT_VERIFY_MINIMALDATA

        If `--minimaldata-flag-strict` is false, immediate data values
        are not subjected to checks: `0x01 VERIFY` will not fail

  --minimaldata-flag-strict=false

        SCRIPT_VERIFY_MINIMALDATA

        Immediate data values are subjected to checks:
        `0x01 VERIFY` will fail, must use `OP_1` (or just `1`) instead

        If true, `--minimaldata-flag` is implied to be true

  --nulldummy-flag=false

        SCRIPT_VERIFY_NULLDUMMY
        If this flag is not set explicitly, it will be false with
        `--sigversion=base`, and true otherwise

  --low-s-flag=true

        SCRIPT_VERIFY_LOW_S
        Only checked with statically-known signatures

  --nullfail-flag=true

        SCRIPT_VERIFY_NULLFAIL

  --cleanstack-flag=true

        SCRIPT_VERIFY_CLEANSTACK
        Will be false if `--is-incomplete-script` is true

  --max-tx-size=1000000

        Maximum transaction size in bytes (used to limit tx weight as
        max_tx_size*4). Only relevant in Elements mode

  --max-num-inputs=24386

        Max possible number of inputs in transaction.
        
        Default value as per https://bitcoin.stackexchange.com/questions/85752/maximum-number-of-inputs-per-transaction
        
        Only relevant in Elements mode, and in Elements the inputs are larger.
        This does not take into account the length of the examined script
        either. So the default value should actually be lower, but still, this
        is OK as an upper bound for now. Might adjust default value later.

  --max-num-outputs=13157

        Max possible number of outputs in transaction.
        
        Default value is a very rough upper bound based on max possible
        non-seqwit size for transaction and min size of output.
        Might adjust default value later.

  --op-plugins=''

        Set of opcode handling plugins to load (paths to python files
        with names ending in '_op_plugin.py')
