# Verification evidence and publication acceptance

The verified local proof graph is fixed by `source-sha256.json`: 18 Lean source/audit files plus the toolchain, Lake configuration, full dependency manifest and two reproduction scripts (23 files). These were copied byte-for-byte into the public package. All were rehashed at publication acceptance and matched the successful local verification. This report reuses that evidence rather than claiming a fresh full build.

## Recorded checks

- `lake build`: exit 0, 3116 jobs.
- `lake build JSP715.CRTAudit JSP715.DifferenceAudit`: exit 0, 3110 jobs.
- `lake env lean -j1 Audit.lean`: exit 0, all 51 explicitly requested declarations present, each with `[propext, Classical.choice, Quot.sound]`.
- Each of the 16 modules in `local-import-closure.txt` was replayed with `lake env leanchecker --verbose MODULE`, exit 0. Every replay log's target was checked. The imports-only aggregator was not used as a broad-prefix replay target.
- Full local proof closure scan found no `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, or compiler proof escape. An empty rg result has exit code 1; this is normalized to success in the recorded result.
- Lean 4.34.0 and the clean Mathlib commit match the toolchain and manifest.
- Final source hashes match and every local dependency is present.

The original verifier runner disappeared after 14 successful substantive-module replays. Process absence was checked before recovery, and previously replayed proof hashes were checked for continuity. Recovery reran `lake build`, completed both audit-module replays, and finished scans, dependency checks and final hashes with exit 0. This interruption is disclosed in `results.json`; incomplete attempts are not counted as passes.

`results.json` is a privacy-safe export of the actual local results: only absolute log locations were replaced by repository-relative log links. Selected logs are included verbatim. Logs containing environment command traces or broad repository prose searches are excluded; their checked result is retained. No private session records or machine-specific paths are needed to reproduce the proof.

No main theorem has an assumed finite construction, assumed extremal estimate or missing lemma. The two convergence hypotheses are the original question's hypotheses, as spelled out in the repository README. A stronger all-large-N sum bound and existence of either limit are not being claimed.
