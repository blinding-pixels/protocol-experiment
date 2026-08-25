# Exact-source CI infrastructure finding

The frozen source commit is `5b5d50e6d03bc5a8691fed8449e10afb9cd9fe0f`.

All five research workflow families created failed job records, but every observed job had no executable steps and no log URL. Therefore the workflows did not produce evidence that Rust, Lean, EasyCrypt, ProVerif, Verus, the attack binaries, target measurements, or packaging commands ran.

This is classified as an infrastructure or runner-configuration failure. It is neither a passing result nor a failing proof or implementation result.

The exact machine-readable observation is `evidence/runnerless-ci-finding.json`.

A successful Rust/Verus artifact does exist for commit `7e7b19e55ee26fb040de12960eccf76d38277661`, and a successful formal-source artifact exists for commit `7f685d35a72a463cbcc1052a81710bb02c0c5b80`. Both predate the frozen source and neither contains the compiled dual-target attack laboratory. They are retained under `evidence/historical/` and are explicitly inadmissible for closing current assumptions.

CI remains disabled. Bring-up must begin with one manual runner diagnostic that proves a command executed, followed by one manual, notification-controlled workflow. Only then may proof and implementation outcomes be interpreted.
