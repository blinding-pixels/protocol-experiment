# Verified text-source snapshot

This directory preserves the complete UTF-8 tracked source tree at local standalone
commit `000b7a169c6a`. It contains 97 text files, including the current assumption
validators, updated formal documents, historical formal source, and the 72-test
report. Four historical binary archive artifacts are intentionally excluded and
remain separately listed as open preservation items.

The archive is base64 encoded and split into twelve ordinary Git files so GitHub's
content API could preserve it without adding CI or relying on an external release
service. Every remote part's Git blob identity was compared with the corresponding
local bytes.

## Restore

From this directory:

```text
cat part-* | base64 --decode > causal-dag-assurance-text-000b7a1.tar.xz
printf '%s  %s\n' db309e499865a3d6fec690d47e39626bb71ff5902a064e4c8b968f69a0c5787b causal-dag-assurance-text-000b7a1.tar.xz | sha256sum -c -
tar -xJf causal-dag-assurance-text-000b7a1.tar.xz
```

Or run `bash RESTORE.sh`.

## Assurance boundary

A matching archive checksum establishes byte preservation only. It does not make
the contained claims true, rerun any theorem prover, compile the mutation targets,
or close production and target-specific obligations. See `MANIFEST.json` and the
repository-level formal claim status.
