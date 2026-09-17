# JSP-000715 / Erdos Problem 863

A complete Lean formalization of the current [JSP-000715](https://github.com/TheJustinSunPrize/awards/blob/82be4c4913b8fe394d68d1391f4c221fde947211/problems/catalog-0701-0800.md#JSP-000715) / [Erdos Problem 863](https://www.erdosproblems.com/863) comparison, with independently implemented local bounded-sum and bounded-difference proofs.

## Full statement and precise scope

For a natural parameter r >= 2 and each N, let S_r(N) be the maximum cardinality of A contained in {1,...,N} such that every sum has at most r representations a+b=n with a<=b and a,b in A. Diagonal pairs count once. Let D_r(N) be the maximum cardinality under the condition that every positive difference d has at most r ordered representations a-b=d. Zero differences are excluded.

If S_r(N)/sqrt(N) tends to cSum and D_r(N)/sqrt(N) tends to cDiff as N tends to infinity, then cDiff<cSum, for every r>=2. These two convergence premises are exactly the original question's conditional asymptotic-constant premises. Neither extremal bound is assumed. The formalization proves the full comparison for all required r, rather than assuming a construction, a bound, or an unproved step.

Theorem: **`JSP715.jsp000715`**, [JSP715/Main.lean](JSP715/Main.lean), line 40.

```lean
theorem JSP715.jsp000715 {r : Nat} (hr : 2 <= r) {cSum cDiff : Real}
    (hsum : JSP715.HasSqrtAsymptotic (JSP715.sumExtremal r) cSum)
    (hdiff : JSP715.HasSqrtAsymptotic (JSP715.diffExtremal r) cDiff) :
    cDiff < cSum
```

`HasSqrtAsymptotic` is explicitly `Filter.Tendsto` of the normalized extremal function. Both extrema are maxima over finite admissible powersets; attainment is proved even at N=0. The natural/integer positive-difference bridge proves equality of entire representation fibers and their cardinalities.

`jsp000715_bounds` proves the quantitative chain

```text
cDiff <= sqrt(r) < (r + floor(r/2))/sqrt(r + 2*floor(r/2)) <= cSum.
```

`jsp000715_constants_ne` proves the constants differ. Independently of either limit, `jsp000715_unbounded_strict` proves that beyond every threshold there is N with D_r(N)<S_r(N). This last statement is not an eventual-all-N claim.

The proof does not assert existence of either limit or the stronger sum liminf theorem from the literature. Those are not required for the current conditional question. The generic CRT02 pasting lemma and its original sparse digit pattern are instantiated with a directly proved Ruzsa base modulo p(p-1), size p-1, for every prime p. This disclosed substitution for the paper's Singer base preserves the exact coefficient. No literature construction theorem or upper bound is assumed.

## Build

Pinned environment: Lean **4.34.0**, Mathlib commit **5ed2965256430c3649e86755f9576b54eca72435**, with the full Lake manifest included. Install elan and Git, then from the repository root:

```sh
lake exe cache get
lake build
lake build JSP715.CRTAudit JSP715.DifferenceAudit
lake env lean -j1 Audit.lean
```

On PowerShell 7, with ripgrep available, the exact additional local-module replay and consistency audit can be run with:

```powershell
./scripts/verify.ps1
```

All local import dependencies are present; all other imports are from pinned Mathlib. There is no external problem-proof download or `ErdosProblems.Erdos863` dependency. No `.lake` cache, PDF, archive, private attachment or prior task transcript is distributed.

## Verification evidence

[Verification report](verification/README.md), [actual results](verification/results.json), [51 direct axiom outputs](verification/axioms-signatures.log), [proof/build-file SHA256 values](verification/source-sha256.json). All 16 local modules were kernel-replayed. The default build, component builds, final theorem audit, source scan and pinned-environment checks succeeded. The only axioms printed are `propext`, `Classical.choice`, and `Quot.sound`.

For publication, existing successful verification was reused after checking every proof source, toolchain and lockfile against its verified hash. No fresh Lean build is claimed for publication. The English documentation and privacy-safe evidence packaging do not change the verified proof files. Kernel replay is a Lean-kernel consistency check against imported dependencies, not a separate theorem prover or a reproof of all Mathlib.

## Attribution

See [ATTRIBUTION.md](ATTRIBUTION.md) for mathematical sources, AI-assisted formalization roles, prior public formal work and exact local contributions. Mathematical attribution is unchanged; this repository owner or PR submitter is not claimed as the original mathematical solver or the first formalization author.
