# B'SST release notes

Version 0.1.3

* Use actual conditions to designate paths, instead of opcodes with args

    Instead of

    ```
    IF wit0 @ 0:L1 : True
    NOTIF wit1 @ 1:L1 : False
    IFDUP wit2 @ 2:L1 : True
    -------------------------
    ```

    Paths will be shown as


    ```
    When wit0 :: [IF @ 0:L1]
     And not wit1 :: [NOTIF @ 1:L1]
     And BOOL(wit2) :: [IFDUP @ 2:L1]
    ---------------------------------
    ```

* Fix settig 520-byte limit for witness 0: Due to trivial error, the 520-byte limit was not set for witness 0 when first accessing it. This limit will be usually set in other places, too, so it is unclear if this would ever surface as a problem, so this is a minor bug, but a bug nevertheless.

* Fix transaction version restriction: standard transaction versions are currenlty only 1 or 2, and for miner mode, transaction versions are not restricted at all

* Fix bug in processing of intersection of enforcements

* Fix data reference display in paths for witness info

* Fix handling of empty signatures for CHECKSIG

* Fix error message on CHECKMULTISIG invalid sig count

* Add --hide-always-true-enforcements setting

* Improve processing of intersection of enforcements in different execution paths

* Restrict introspected scriptpubkey length for inputs (when --is-miner=false)

* Show full paths for "Finalizing path" messages in log

* Display unused values per-path instead of 'unused in all paths'

Version 0.1.2

* Rework plugin system, now plugins are 'general' in a sense that they can hook into different stages of analysis to observe or change various things. Please look at `plugins` directory for details

* Add ability to set assertions on stack values and witnesses, and assumptions for data placeholders. Please see newly added "Assertions" and "Assumptions" sections in README. You might also look at `tests/test_assertions_and_assumptions.py` for examples of usage

* Add ability to analyze opcodes that access the stack differently based on their arguments, like `PICK`, `ROLL`, `CHECKMULTISIG`, even if these arguments are not statically known. When z3 is enabled, model values for these arguments will be generated, and separate execution path for each generated value will be created. Maximum number of samples to generate is set with `--max-samples-for-dynamic-stack-access`. When z3 is not enabled, analysis will stop with an error when these opcodes with non-static arguments are encountered.

* Add ability to set aliases for witnesses with `// bsst-name-alias(wit<N>): alias_name` (where <N> is withess number). For example, aliased witnesses 0 will be shown in the report as `alias_name<wit0>`

* New setting: `--produce-model-values-for`. It is a set of glob patterns to specify which model values to produce. Please look at the help text for this setting for details. Data references now are not included in the default set to produce model values for, but can be enabled with `$*` pattern.

* More than one model value sample can be generated per analyzed value, if max number of samples is specified after `:` in the pattern given with `--produce-model-values-for` setting. The limitation of multiple samples is that samples are generated independently, that means for `$a $b ADD VERIFY` your can get `1, 0` as possible values for both `$a` and `$b`, even if they cannot be both 0 at the same time

* The setting `--points-of-interest` can now take `*` as argument: that means that execution state for all opcodes will be reported (don't forget to quote `*` in the shell to avoid shell glob pattern expansion)

* Byte sizes of model value samples will be shown in the report when `--report-model-value-sizes` is set to `true`

* Settings that accept a comma-separated set of values, when the setting argument is given twice, now update the set rather than replace it

* Improved reporting for data references. Now data references are printed at the end of the report

* Add setting to set comment marker: `--comment-marker`. Note that comments are removed before parsing the rest of the line, and because of this, comment markers cannot appear within quoted strings

* Fix: scriptnum decoding was not imposing "0 >= x => 255" bound on the byte sequence if its size was 1. This was causing problems with `bsst-assume` tests, but likely that this could have caused problems elsewhere, too

* To avoid confusion, data reference names cannot be `wit<N>` (where `<N>` is a number), because such names are reserved for witnesses

* Fixes in parser: quotes within quotes were allowed, but should not; angle brackets were sometimes not ignored

* Fix: in reported "Valid paths", execution path branches where only one path is valid were skipped. That was confusing, now full paths are showin in "Valid paths"

* Fix: data placholders with same names should be assumed equal, but were not

* Fix: giving numbers (offsets) in `--points-of-interest` were broken, fixed

* Other minor improvements and fixes

Version 0.1.1:

* Fixed a bug with number of used witnesses shown incorrectly in the report when Z3 is disabled

* Fixed a bug where analysing statically-known Schnorr 64-byte signatures caused a crash

* Fixed a bug where "high S" condition on ECDSA signatures was incorrectly detected. Now `LOW_S` check
  that is enabled with `--low-s-flag=true` is only done with statically-known signatures. Doing proper
  symbolic checks for this would be too complex and would severely affect performance. At the same time,
  `LOW_S` script flag is only relevant for ECDSA signatures, therefore the usefulness of this detection is limited

* Improved hashtype checks for Schnorr signatures

* Added detection of "CHECKSIG with same sig, pubkey, hashtype must always give same result" and
  "If CHECKSIG is successful with particular sig, it must fail if different pubkey and hashtype is used with this sig"

* "Data identifiers" are now called "Data references" and is preceded with `&` in the report.
  Like this: `OP_ADD // =>add_result` will be shown as `&add_result` in the report. The section
  "Data references" will have these reference names without `&` in the first column, but with `&`
  afther the `=`.

Version 0.1.0: initial release
