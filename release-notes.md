# B'SST release notes
Version 0.1.0.dev0:

* `--low-s-flag` now only checked with statically-known signatures. Doing proper symbolic checks
  would be too complex and would severely affect performance. At the same time, this check is
  only relevant for ECDSA signatures, therefore its usefulness is limited

* "Data identifiers" are now called "Data references" and is preceded with `&` in the report.
  Like this: `OP_ADD // =>add_result` will be shown as `&add_result` in the report. The section
  "Data references" will have these reference names without `&` in the first column, but with `&`
  afther the `=`.

Version 0.1.0: initial release
