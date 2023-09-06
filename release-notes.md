# B'SST release notes
Version 0.1.0.dev0:

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
