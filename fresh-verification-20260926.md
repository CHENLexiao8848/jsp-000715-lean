# Fresh verification of JSP-000715 on 2026-09-26

Selected proof: `d202e2c1b904389c6d21f74ab856e3099b0b8391` in `CHENLexiao8848/jsp-000715-lean`, branch `codex/jsp-000715-proof`.

A new isolated checkout was built on Darwin arm64 using Lean 4.34.0 and the nine exact dependency revisions below. Before the project build, the project's `.lake/build` directory was absent and no local project `.olean` existed. Dependency artifacts were obtained by the official Mathlib content-addressed cache tool at the pinned source revision. `lake --no-cache build` succeeded, followed by a separate three-target Lean audit. The full build log below identifies every local project module as `Built`.

This is a fresh compilation of the submitted project using pinned dependency caches, not a build of all Mathlib from source. No new full 51-declaration audit, all-module replay, independent human review, maintainer acceptance or award eligibility is asserted. The one nonfatal linter warning is retained in the unedited build log. Source and lock hashes before/after are identical; tracked Git state was clean and all 23 release-manifest entries matched.

The report is a later documentation artifact about the original proof SHA. The historical report and its interrupted-run recovery remain separate. Two stalled optional cache-download attempts were stopped before project compilation; the successful attempt used the official cache tool's documented direct Azure backend for identical content-addressed artifacts.

## Executed project commands

From the isolated pinned project directory, with the verified official toolchain in PATH:

```sh
lake --no-cache build
lake env lean ../build-evidence/TerminalAudit.lean
```

Both exited 0. The audit file's full contents are included below; its parent-directory location keeps the selected proof tree unchanged. For reproduction on another machine, use the fixed project's normal dependency setup, start with no local project build artifacts, and place the audit file at the shown sibling path or pass its actual path to `lake env lean`.


## fresh-verification-summary.json

SHA-256: `e4c525ac31f6ade68469c786ceb94e7e8accf10c6cd1945103dbc53d02091ac0`

```json
{
  "problem": "JSP-000715",
  "pull_request": 773,
  "repository": "https://github.com/CHENLexiao8848/jsp-000715-lean",
  "proof_sha": "d202e2c1b904389c6d21f74ab856e3099b0b8391",
  "verified_at": "2026-09-26T05:19:01.340160+00:00",
  "status": "passed",
  "platform": "Darwin arm64",
  "lean": "Lean (version 4.34.0, arm64-apple-darwin24.6.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)",
  "official_toolchain_sha256": "69f263fa6e21bbc2466bbfb1affcd92479ee2714c883a07de548e099a5922932",
  "mathlib_sha": "5ed2965256430c3649e86755f9576b54eca72435",
  "all_nine_dependency_revisions_match_lock": true,
  "publication_manifest_matches": "23/23",
  "project_oleans_before_build": 0,
  "build_command": [
    "lake",
    "--no-cache",
    "build"
  ],
  "build_exit_code": 0,
  "build_jobs": 3116,
  "terminal_audit_command": [
    "lake",
    "env",
    "lean",
    "../build-evidence/TerminalAudit.lean"
  ],
  "terminal_audit_exit_code": 0,
  "terminal_axioms": {
    "JSP715.jsp000715": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "JSP715.jsp000715_bounds": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "JSP715.jsp000715_constants_ne": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ]
  },
  "source_and_lock_hashes_unchanged": true,
  "tracked_worktree_clean": true,
  "source_scan": "No sorry, admit, native_decide, axiom, or unsafe declaration matches in local Lean source scan.",
  "scope": "Fresh compilation of the submitted project using cached artifacts for hash-pinned Mathlib dependencies. This is not a from-source Mathlib build, new independent human review, or a new kernel replay of every module.",
  "warnings": [
    "One nonfatal unnecessarySeqFocus linter warning at JSP715/CRTConstruction.lean:60:32."
  ],
  "environment_recoveries": [
    "Stopped stalled optional Reservoir dependency artifact request and disabled automatic Lake build caches.",
    "Stopped a stalled cache CDN download and used the official cache tool documented direct Azure backend for identical content-addressed artifacts."
  ],
  "artifact_sha256": {
    "clean-project-build.log": "09a33e590f5ed27dc4e29871097786678cdbc631f39ec4f31c53c4629f156b42",
    "terminal-audit.log": "fea737e40359451dc2af4c490fc31e544f0dfb0b67164bd1c5b92c88038f3abd",
    "TerminalAudit.lean": "25fb8125afd37932e7733cd5f52c46a9f8afb4d72164f3e4ff733336b24760dc",
    "dependencies.json": "4aeef5e4e426713da6dcf8cda7adfe382ac5345fedf910ab73044d32c9979b93",
    "source-hashes-before.json": "d01766318a8b4d598fd831a650c67f5a3b8dee274bd85611c9ee0c70dd3e9d45",
    "source-hashes-after.json": "d01766318a8b4d598fd831a650c67f5a3b8dee274bd85611c9ee0c70dd3e9d45",
    "publication-manifest-check.json": "21dcf913291e93d7be8ed6534fdbcaf41d076fdd935e6f913880e90fbb574e8d"
  }
}
```


## clean-project-build.log

SHA-256: `09a33e590f5ed27dc4e29871097786678cdbc631f39ec4f31c53c4629f156b42`

```text
ℹ [3101/3116] Built JSP715.CRTConvention (7.9s)
info: JSP715/CRTConvention.lean:118:0: 'JSP715.CRTConvention.interval_convention' depends on axioms: [propext, Classical.choice, Quot.sound]
ℹ [3102/3116] Built JSP715.CRTBase (12s)
info: JSP715/CRTBase.lean:112:0: 'JSP715.CRT.exists_base' depends on axioms: [propext, Classical.choice, Quot.sound]
✔ [3103/3116] Built JSP715.CRTCoefficient (12s)
✔ [3104/3116] Built JSP715.Comparison (12s)
✔ [3105/3116] Built JSP715.DifferenceUpper (12s)
✔ [3106/3116] Built JSP715.CRTPattern (12s)
✔ [3107/3116] Built JSP715.DifferenceBridge (3.6s)
⚠ [3108/3116] Built JSP715.CRTConstruction (4.3s)
warning: JSP715/CRTConstruction.lean:60:32: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
✔ [3109/3116] Built JSP715.CRTAsymptotic (3.6s)
✔ [3110/3116] Built JSP715.CRTInterface (3.8s)
✔ [3111/3116] Built JSP715.Basic (5.1s)
✔ [3112/3116] Built JSP715.SumAsymptotic (4.7s)
✔ [3113/3116] Built JSP715.Asymptotic (4.8s)
✔ [3114/3116] Built JSP715.Main (4.8s)
✔ [3115/3116] Built JSP715 (4.6s)
Build completed successfully (3116 jobs).
```


## TerminalAudit.lean

SHA-256: `25fb8125afd37932e7733cd5f52c46a9f8afb4d72164f3e4ff733336b24760dc`

```lean
import JSP715

#check JSP715.jsp000715
#check JSP715.jsp000715_bounds
#check JSP715.jsp000715_constants_ne
#print axioms JSP715.jsp000715
#print axioms JSP715.jsp000715_bounds
#print axioms JSP715.jsp000715_constants_ne
```


## terminal-audit.log

SHA-256: `fea737e40359451dc2af4c490fc31e544f0dfb0b67164bd1c5b92c88038f3abd`

```text
JSP715.jsp000715 {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ} (hsum : JSP715.HasSqrtAsymptotic (JSP715.sumExtremal r) cSum)
  (hdiff : JSP715.HasSqrtAsymptotic (JSP715.diffExtremal r) cDiff) : cDiff < cSum
JSP715.jsp000715_bounds {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ}
  (hsum : JSP715.HasSqrtAsymptotic (JSP715.sumExtremal r) cSum)
  (hdiff : JSP715.HasSqrtAsymptotic (JSP715.diffExtremal r) cDiff) :
  cDiff ≤ √↑r ∧ √↑r < JSP715.crtConstant r ∧ JSP715.crtConstant r ≤ cSum
JSP715.jsp000715_constants_ne {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ}
  (hsum : JSP715.HasSqrtAsymptotic (JSP715.sumExtremal r) cSum)
  (hdiff : JSP715.HasSqrtAsymptotic (JSP715.diffExtremal r) cDiff) : cSum ≠ cDiff
'JSP715.jsp000715' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP715.jsp000715_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP715.jsp000715_constants_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
```


## dependencies.json

SHA-256: `4aeef5e4e426713da6dcf8cda7adfe382ac5345fedf910ab73044d32c9979b93`

```json
[
  {
    "name": "mathlib",
    "url": "https://github.com/leanprover-community/mathlib4.git",
    "expected_rev": "5ed2965256430c3649e86755f9576b54eca72435",
    "actual_rev": "5ed2965256430c3649e86755f9576b54eca72435",
    "success": true
  },
  {
    "name": "plausible",
    "url": "https://github.com/leanprover-community/plausible",
    "expected_rev": "118aa17ee84656b8bd727fef7c458ee8c833385c",
    "actual_rev": "118aa17ee84656b8bd727fef7c458ee8c833385c",
    "success": true
  },
  {
    "name": "LeanSearchClient",
    "url": "https://github.com/leanprover-community/LeanSearchClient",
    "expected_rev": "ddf04cf3949fa556442341e87d47f9f6e6074707",
    "actual_rev": "ddf04cf3949fa556442341e87d47f9f6e6074707",
    "success": true
  },
  {
    "name": "importGraph",
    "url": "https://github.com/leanprover-community/import-graph",
    "expected_rev": "e928b72544873815af278d38681b31c0293588e3",
    "actual_rev": "e928b72544873815af278d38681b31c0293588e3",
    "success": true
  },
  {
    "name": "proofwidgets",
    "url": "https://github.com/leanprover-community/ProofWidgets4",
    "expected_rev": "106ff4fafc74ef4ac99d81dbf3ab399118f497a5",
    "actual_rev": "106ff4fafc74ef4ac99d81dbf3ab399118f497a5",
    "success": true
  },
  {
    "name": "aesop",
    "url": "https://github.com/leanprover-community/aesop",
    "expected_rev": "355695d523e41d0554926416cba2a2b3544fbbc9",
    "actual_rev": "355695d523e41d0554926416cba2a2b3544fbbc9",
    "success": true
  },
  {
    "name": "Qq",
    "url": "https://github.com/leanprover-community/quote4",
    "expected_rev": "6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259",
    "actual_rev": "6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259",
    "success": true
  },
  {
    "name": "batteries",
    "url": "https://github.com/leanprover-community/batteries",
    "expected_rev": "f2effa3d803fda822b1f97b806c47cf2adfbcbc2",
    "actual_rev": "f2effa3d803fda822b1f97b806c47cf2adfbcbc2",
    "success": true
  },
  {
    "name": "Cli",
    "url": "https://github.com/leanprover/lean4-cli",
    "expected_rev": "e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204",
    "actual_rev": "e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204",
    "success": true
  }
]
```


## source-hashes-before.json

SHA-256: `d01766318a8b4d598fd831a650c67f5a3b8dee274bd85611c9ee0c70dd3e9d45`

```json
{
  "Audit.lean": "2d204941fcfa2fdc161232038614e356d646855ea1af17587215b010fb930152",
  "JSP715/Asymptotic.lean": "a4f5131ad9043fd280ef09a12edbd429826a8bd431388c95ba8f1cb511ddc176",
  "JSP715/Basic.lean": "6f5bf2a50b93b6ee06e80713a9c886959efefe45868c8f83e4d21c7e89aed28f",
  "JSP715/CRTAsymptotic.lean": "b4b81945a57cceae222944689db97d6052c59da0e8e88e7fe1a51451395846b6",
  "JSP715/CRTAudit.lean": "ddce0eb576736d1d19776dfd1d26516069fe587b957d721d9e8560c8ba2258eb",
  "JSP715/CRTBase.lean": "911fe92552e1669db0769d9d9474a859625e54786a359b90005e92f593bc1d61",
  "JSP715/CRTCoefficient.lean": "ef7fad4aaa88bfc458e3e92cb95d1f9779108f44723db4a5f5515385c119148d",
  "JSP715/CRTConstruction.lean": "9b0716ad18845a74453d387c021b05fd19b24bf5e98bc9719a8313b7d375727d",
  "JSP715/CRTConvention.lean": "333fdafeda94b04326cf0fe8ed4dffc419730f429bd18c4e9d73e30abd7c1587",
  "JSP715/CRTInterface.lean": "066ca45467925d2e14bdaf922ad6094fd518576b6a00deccd63f51a6f9fba79c",
  "JSP715/CRTPattern.lean": "b1833e2609572ee7dceedd1710af3a873703d39cdc9a21af4235ca0287e05b97",
  "JSP715/Comparison.lean": "76e7c85050264215d93c9403e7a59c9ea6b8ee73da090356e7491d2b1bc42b56",
  "JSP715/DifferenceAudit.lean": "d597a3551982083fea66880b88957a1e93523a04ff70e2cf18a4be2581014f23",
  "JSP715/DifferenceBridge.lean": "b3fe0663a9a7f98d0fc3f7a2c97addb7e76d080ccb053fd17b4ae50f8763312d",
  "JSP715/DifferenceUpper.lean": "e181c2b75011db0e4a130529100850a38e00605f1b679264d5d20bbbb9161906",
  "JSP715/Main.lean": "10f0ff10aef143fdbd9915d2bdae92a11aea1b191497564cf6a73eccf246ccb6",
  "JSP715/SumAsymptotic.lean": "802460cd749a278866a6003d13325328ff844576d97e243c0c5820f56f01be44",
  "JSP715.lean": "766209c091ce99f0ab5364ceec167cc393fcf732ef544b19b47977003510c7dc",
  "lake-manifest.json": "e94beb21b3f2d043d6eee55c0ca29ec3eab91d1ea1c4edef190984fbe2ab59ec",
  "lakefile.toml": "a7af5b3d5316759104c97ecb44d172ca68b38f219c553be2b01f7fb950caafbc",
  "lean-toolchain": "8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632"
}
```


## source-hashes-after.json

SHA-256: `d01766318a8b4d598fd831a650c67f5a3b8dee274bd85611c9ee0c70dd3e9d45`

```json
{
  "Audit.lean": "2d204941fcfa2fdc161232038614e356d646855ea1af17587215b010fb930152",
  "JSP715/Asymptotic.lean": "a4f5131ad9043fd280ef09a12edbd429826a8bd431388c95ba8f1cb511ddc176",
  "JSP715/Basic.lean": "6f5bf2a50b93b6ee06e80713a9c886959efefe45868c8f83e4d21c7e89aed28f",
  "JSP715/CRTAsymptotic.lean": "b4b81945a57cceae222944689db97d6052c59da0e8e88e7fe1a51451395846b6",
  "JSP715/CRTAudit.lean": "ddce0eb576736d1d19776dfd1d26516069fe587b957d721d9e8560c8ba2258eb",
  "JSP715/CRTBase.lean": "911fe92552e1669db0769d9d9474a859625e54786a359b90005e92f593bc1d61",
  "JSP715/CRTCoefficient.lean": "ef7fad4aaa88bfc458e3e92cb95d1f9779108f44723db4a5f5515385c119148d",
  "JSP715/CRTConstruction.lean": "9b0716ad18845a74453d387c021b05fd19b24bf5e98bc9719a8313b7d375727d",
  "JSP715/CRTConvention.lean": "333fdafeda94b04326cf0fe8ed4dffc419730f429bd18c4e9d73e30abd7c1587",
  "JSP715/CRTInterface.lean": "066ca45467925d2e14bdaf922ad6094fd518576b6a00deccd63f51a6f9fba79c",
  "JSP715/CRTPattern.lean": "b1833e2609572ee7dceedd1710af3a873703d39cdc9a21af4235ca0287e05b97",
  "JSP715/Comparison.lean": "76e7c85050264215d93c9403e7a59c9ea6b8ee73da090356e7491d2b1bc42b56",
  "JSP715/DifferenceAudit.lean": "d597a3551982083fea66880b88957a1e93523a04ff70e2cf18a4be2581014f23",
  "JSP715/DifferenceBridge.lean": "b3fe0663a9a7f98d0fc3f7a2c97addb7e76d080ccb053fd17b4ae50f8763312d",
  "JSP715/DifferenceUpper.lean": "e181c2b75011db0e4a130529100850a38e00605f1b679264d5d20bbbb9161906",
  "JSP715/Main.lean": "10f0ff10aef143fdbd9915d2bdae92a11aea1b191497564cf6a73eccf246ccb6",
  "JSP715/SumAsymptotic.lean": "802460cd749a278866a6003d13325328ff844576d97e243c0c5820f56f01be44",
  "JSP715.lean": "766209c091ce99f0ab5364ceec167cc393fcf732ef544b19b47977003510c7dc",
  "lake-manifest.json": "e94beb21b3f2d043d6eee55c0ca29ec3eab91d1ea1c4edef190984fbe2ab59ec",
  "lakefile.toml": "a7af5b3d5316759104c97ecb44d172ca68b38f219c553be2b01f7fb950caafbc",
  "lean-toolchain": "8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632"
}
```


## publication-manifest-check.json

SHA-256: `21dcf913291e93d7be8ed6534fdbcaf41d076fdd935e6f913880e90fbb574e8d`

```json
{
  "total": 23,
  "all_match": true,
  "files": [
    {
      "path": "JSP715/CRTBase.lean",
      "expected": "911fe92552e1669db0769d9d9474a859625e54786a359b90005e92f593bc1d61",
      "actual": "911fe92552e1669db0769d9d9474a859625e54786a359b90005e92f593bc1d61",
      "match": true
    },
    {
      "path": "JSP715/CRTPattern.lean",
      "expected": "b1833e2609572ee7dceedd1710af3a873703d39cdc9a21af4235ca0287e05b97",
      "actual": "b1833e2609572ee7dceedd1710af3a873703d39cdc9a21af4235ca0287e05b97",
      "match": true
    },
    {
      "path": "JSP715/CRTConstruction.lean",
      "expected": "9b0716ad18845a74453d387c021b05fd19b24bf5e98bc9719a8313b7d375727d",
      "actual": "9b0716ad18845a74453d387c021b05fd19b24bf5e98bc9719a8313b7d375727d",
      "match": true
    },
    {
      "path": "JSP715/CRTCoefficient.lean",
      "expected": "ef7fad4aaa88bfc458e3e92cb95d1f9779108f44723db4a5f5515385c119148d",
      "actual": "ef7fad4aaa88bfc458e3e92cb95d1f9779108f44723db4a5f5515385c119148d",
      "match": true
    },
    {
      "path": "JSP715/CRTAsymptotic.lean",
      "expected": "b4b81945a57cceae222944689db97d6052c59da0e8e88e7fe1a51451395846b6",
      "actual": "b4b81945a57cceae222944689db97d6052c59da0e8e88e7fe1a51451395846b6",
      "match": true
    },
    {
      "path": "JSP715/CRTConvention.lean",
      "expected": "333fdafeda94b04326cf0fe8ed4dffc419730f429bd18c4e9d73e30abd7c1587",
      "actual": "333fdafeda94b04326cf0fe8ed4dffc419730f429bd18c4e9d73e30abd7c1587",
      "match": true
    },
    {
      "path": "JSP715/CRTInterface.lean",
      "expected": "066ca45467925d2e14bdaf922ad6094fd518576b6a00deccd63f51a6f9fba79c",
      "actual": "066ca45467925d2e14bdaf922ad6094fd518576b6a00deccd63f51a6f9fba79c",
      "match": true
    },
    {
      "path": "JSP715/DifferenceUpper.lean",
      "expected": "e181c2b75011db0e4a130529100850a38e00605f1b679264d5d20bbbb9161906",
      "actual": "e181c2b75011db0e4a130529100850a38e00605f1b679264d5d20bbbb9161906",
      "match": true
    },
    {
      "path": "JSP715/DifferenceBridge.lean",
      "expected": "b3fe0663a9a7f98d0fc3f7a2c97addb7e76d080ccb053fd17b4ae50f8763312d",
      "actual": "b3fe0663a9a7f98d0fc3f7a2c97addb7e76d080ccb053fd17b4ae50f8763312d",
      "match": true
    },
    {
      "path": "JSP715/Basic.lean",
      "expected": "6f5bf2a50b93b6ee06e80713a9c886959efefe45868c8f83e4d21c7e89aed28f",
      "actual": "6f5bf2a50b93b6ee06e80713a9c886959efefe45868c8f83e4d21c7e89aed28f",
      "match": true
    },
    {
      "path": "JSP715/Comparison.lean",
      "expected": "76e7c85050264215d93c9403e7a59c9ea6b8ee73da090356e7491d2b1bc42b56",
      "actual": "76e7c85050264215d93c9403e7a59c9ea6b8ee73da090356e7491d2b1bc42b56",
      "match": true
    },
    {
      "path": "JSP715/Asymptotic.lean",
      "expected": "a4f5131ad9043fd280ef09a12edbd429826a8bd431388c95ba8f1cb511ddc176",
      "actual": "a4f5131ad9043fd280ef09a12edbd429826a8bd431388c95ba8f1cb511ddc176",
      "match": true
    },
    {
      "path": "JSP715/SumAsymptotic.lean",
      "expected": "802460cd749a278866a6003d13325328ff844576d97e243c0c5820f56f01be44",
      "actual": "802460cd749a278866a6003d13325328ff844576d97e243c0c5820f56f01be44",
      "match": true
    },
    {
      "path": "JSP715/Main.lean",
      "expected": "10f0ff10aef143fdbd9915d2bdae92a11aea1b191497564cf6a73eccf246ccb6",
      "actual": "10f0ff10aef143fdbd9915d2bdae92a11aea1b191497564cf6a73eccf246ccb6",
      "match": true
    },
    {
      "path": "JSP715.lean",
      "expected": "766209c091ce99f0ab5364ceec167cc393fcf732ef544b19b47977003510c7dc",
      "actual": "766209c091ce99f0ab5364ceec167cc393fcf732ef544b19b47977003510c7dc",
      "match": true
    },
    {
      "path": "JSP715/CRTAudit.lean",
      "expected": "ddce0eb576736d1d19776dfd1d26516069fe587b957d721d9e8560c8ba2258eb",
      "actual": "ddce0eb576736d1d19776dfd1d26516069fe587b957d721d9e8560c8ba2258eb",
      "match": true
    },
    {
      "path": "JSP715/DifferenceAudit.lean",
      "expected": "d597a3551982083fea66880b88957a1e93523a04ff70e2cf18a4be2581014f23",
      "actual": "d597a3551982083fea66880b88957a1e93523a04ff70e2cf18a4be2581014f23",
      "match": true
    },
    {
      "path": "Audit.lean",
      "expected": "2d204941fcfa2fdc161232038614e356d646855ea1af17587215b010fb930152",
      "actual": "2d204941fcfa2fdc161232038614e356d646855ea1af17587215b010fb930152",
      "match": true
    },
    {
      "path": "lean-toolchain",
      "expected": "8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632",
      "actual": "8733782dc070a99b312039cda424f601b80f3be6f6f512627da5ba25adc27632",
      "match": true
    },
    {
      "path": "lakefile.toml",
      "expected": "a7af5b3d5316759104c97ecb44d172ca68b38f219c553be2b01f7fb950caafbc",
      "actual": "a7af5b3d5316759104c97ecb44d172ca68b38f219c553be2b01f7fb950caafbc",
      "match": true
    },
    {
      "path": "lake-manifest.json",
      "expected": "e94beb21b3f2d043d6eee55c0ca29ec3eab91d1ea1c4edef190984fbe2ab59ec",
      "actual": "e94beb21b3f2d043d6eee55c0ca29ec3eab91d1ea1c4edef190984fbe2ab59ec",
      "match": true
    },
    {
      "path": "scripts/bootstrap.ps1",
      "expected": "8753a4e562e0ce8b7fddeb4c9749274d9bb36e8958ef9c0cdf0014366be1ab2a",
      "actual": "8753a4e562e0ce8b7fddeb4c9749274d9bb36e8958ef9c0cdf0014366be1ab2a",
      "match": true
    },
    {
      "path": "scripts/verify.ps1",
      "expected": "9e5a9afc41f6abf9d097ed5bf9f16570d68aaeed1b42b0cb8ff9a1a093045e88",
      "actual": "9e5a9afc41f6abf9d097ed5bf9f16570d68aaeed1b42b0cb8ff9a1a093045e88",
      "match": true
    }
  ]
}
```
