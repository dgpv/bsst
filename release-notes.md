# B'SST release notes

Version 0.1.2.dev0:

* Rework plugin system, now plugins are 'general' in a sense that they can hook into different stages of analysis to observe or change various things. Please look at `plugins` directory for details

* Add ability to set assertions on stack values and witnesses, and assumptions for data placeholders. Please see newly added "Assertions" and "Assumptions" sections in README. You might also look at `tests/test_assertions_and_assumptions.py` for examples of usage

* New setting: `--produce-model-values-for`. It is a set of glob patterns to specify which model values to produce. Please look at the help text for this setting for details. Data references now are not included in the default set to produce model values for, but can be enabled with `$*` pattern.

* The setting `--points-of-interest` can now take `*` as argument: that means that execution state for all opcodes will be reported (don't forget to quote `*` in the shell to avoid shell glob pattern expansion)

* More than one model value sample can be generated analyzed value, if max number of samples is specified after `:` in the pattern in `--produce-model-values-for`

* Byte sizes of model value samples will be shown in the report when `--report-model-value-sizes` is set to `true`

* Settings that accept a comma-separated set of values, when the setting argument is given twice, now update the set rather than replace it

* Add settings to set comment marker. Note that comments are removed before parsing the rest of the line, and because of this, comment markers cannot appear within quoted strings

* Fix: scriptnum decoding was not imposing "0 >= x => 255" bound on the byte sequence if its size was 1. This was causing problems with `bsst-assume` tests, but likely that this could have caused problems elsewhere, too

* To avoid confusion, data reference names cannot be `wit<N>` (where `<N>` is a number), because such names are reserved for witnesses

* Fixes in parser: quotes within quotes were allowed, but should not; angle brackets were sometimes not ignored

* Fix: data placholders with same names should be assumed equal, but were not

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
