# B'SST release notes
Version 0.1.0.dev0:

* `--low-s-flag` now only checked with statically-known signatures. Doing proper symbolic checks
  would be too complex and would severely affect performance. At the same time, this check is
  only relevant for ECDSA signatures, therefore its usefulness is limited

Version 0.1.0: initial release
