# JSP-000715 / Erdős 863: mathematical correspondence and contribution supplement

Date: 2026-09-26. Selected proof version: [`CHENLexiao8848/jsp-000715-lean`](https://github.com/CHENLexiao8848/jsp-000715-lean), branch `codex/jsp-000715-proof`, commit `d202e2c1b904389c6d21f74ab856e3099b0b8391` (called **A** below). This document is supporting prose about A. Publishing it at a later documentation commit does not change the selected proof version or assert a new Lean build. Mathematical review, formalization attribution and acceptance remain for maintainers.

## Mathematical solution and precise source locations

The complete comparison is given in B. S. Ho, *On a problem of Erdős, Berend, and Freud concerning bounded sums and bounded differences*, [public manuscript](https://boonsuan.github.io/erdos863.pdf): Theorem 1 and Corollary 1 on p.2, difference estimate in Lemma 1 on p.3, sum construction in Lemmas 2–4 on pp.4–6, and strict coefficient comparison on p.6. The version retrieved on 2026-09-26 has SHA-256 `eae9479b2ae77e5c2cc5b5d57eaa870064f8ce719d49957d4ed7d49c18b14de7`. No publication date not present in the manuscript is invented. Its disclosed GPT-5.4 Pro contribution is preserved, and the existing catalog's Ho/GPT-5.4 Pro credit is not reassigned.

The historical question is P. Erdős, *Some of my forgotten problems in number theory*, Hardy–Ramanujan Journal 15 (1992), 34–50, pp.39–40, [DOI](https://doi.org/10.46298/hrj.1992.125), indexed as [Erdős Problem 863](https://www.erdosproblems.com/863). The relevant earlier construction is J. Cilleruelo, I. Z. Ruzsa and C. Trujillo, *Upper and Lower Bounds for Finite B_h[g] Sequences*, J. Number Theory 97 (2002), 26–34, [DOI](https://doi.org/10.1006/jnth.2001.2767). In the [author manuscript](https://matematicas.uam.es/~franciscojavier.cilleruelo/Papers/bh.pdf), Theorem 2.1 is on p.4 and Lemmas 2.2–2.3 are on pp.5–6. The retrieved file has SHA-256 `981cc66bc42d340aadefa8914711f864af659d7d028acb295afc7193fb0637e5`.

Ho's paper proves a stronger limsup/liminf separation. The selected Lean proof establishes the original conditional comparison, with a different finite modular base and only the subsequence lower bound needed for that comparison. It does not assert a formalization of every stronger statement in Ho's paper.

## Exact statement and all hypotheses

For each natural `r` and `N`, define `S_r(N)` as the largest cardinality of an admissible subset of `[1,N]` with at most `r` representations of each sum, counted with `a≤b`. Diagonal pairs occur once. Define `D_r(N)` similarly using at most `r` ordered representations of each strictly positive difference. Negative differences have the same multiplicities by swapping the pair, so this is equivalent to bounding all nonzero differences. Including zero would change the problem and is not done.

The finite powersets contain the empty set, so both maxima exist, also for `N=0`. `JSP715.Basic` proves attainment, cardinality bounds and exact transport between natural positive subtraction and integer subtraction; there is no silent reliance on truncated natural subtraction at zero.

For every natural `r≥2` and real `cSum,cDiff`, assume

`S_r(N)/sqrt(N) → cSum` and `D_r(N)/sqrt(N) → cDiff`.

These are the original question's two existence-of-asymptotic-constants premises. No construction, upper estimate, lower estimate or missing theorem is hypothesized. They are retained rather than presented as proven. The conclusion is `cDiff<cSum`, hence `cSum≠cDiff`. The stronger quantitative target proves the entire chain through the CRT coefficient.

## Why the component proofs suffice

Write `s=floor(r/2)`, `K=r+2s`, and `L=r+s`.

For the difference estimate, the local second-moment proof counts intersections of a set `B` with sliding intervals of length `H`. Writing `M=|B|`, it establishes

`M² H² ≤ (N+H−1)(M H+r H(H−1))`.

The positive-difference multiplicity bound controls the off-diagonal term; the diagonal contributes `MH`. The initial total-difference count gives `M=O_r(sqrt(N))`. Choosing an interval length growing faster than `sqrt(N)` but slower than `N` makes the error negligible, giving an eventual bound by `(sqrt(r)+epsilon)sqrt(N)`. Thus any limiting difference constant satisfies `cDiff≤sqrt(r)`. These estimates are proved in `DifferenceUpper` and transported through `DifferenceBridge`; they are not imported as axioms.

For the sum construction, `CRTPattern` uses the precise CRT02 sparse layer

`I_r={0,…,r−1} ∪ {r−1+2j : 1≤j≤s}`.

It proves `|I_r|=L`, `I_r⊆[0,K−1]`, and at most `r` **ordered** layer representations of each sum. `CRTBase` proves a modular Sidon set `C_p` of size `p−1` modulo `q=p(p−1)` for each prime `p`, using the Ruzsa finite-field/Chinese-remainder construction. `CRTConstruction` pastes the layers and translates by one:

`A_p={c+qu+1 : c∈C_p, u∈I_r}`.

It proves `A_p⊆[1,qK]`, `|A_p|=(p−1)L`, and the required bound on **unordered** numerical sums. In the pasting proof the modular Sidon property fixes an unordered residue pair; sorting by residue injects numerical representations into ordered layer-pair representations. The tie case includes a diagonal exactly once. Thus the different representation conventions in the layer and in the final set are connected by a proved injection.

As primes tend to infinity,

`(p−1)L / sqrt(p(p−1)K) → L/sqrt(K)`.

The finite witnesses exist at unbounded lengths. If the full normalized sum extremum converges to `cSum`, its restriction to these lengths has the same limit, so `L/sqrt(K)≤cSum`. This argument needs no all-large-`N` sum construction or prime-gap theorem. Finally `s≥1` and

`(L/sqrt(K))²−r=s²/(r+2s)>0`,

so `sqrt(r)<L/sqrt(K)` and the full quantitative chain follows. `jsp000715_unbounded_strict` is an additional unconditional statement at unbounded lengths, not an eventual-all-lengths theorem and not a substitute for the three submitted terminal goals.

## Theorem correspondence

All links below refer to proof commit A.

| Obligation | Source / declarations |
| --- | --- |
| Sum, difference conventions; attained maxima | [`JSP715/Basic.lean`](https://github.com/CHENLexiao8848/jsp-000715-lean/blob/d202e2c1b904389c6d21f74ab856e3099b0b8391/JSP715/Basic.lean); `mem_sumReps`, `diagonal_mem_sumReps`, `isDiffB2_iff_integer`, `exists_sumExtremal_set`, `exists_diffExtremal_set` |
| Finite second-moment bound and eventual upper bound | `JSP715/DifferenceUpper.lean`, `DifferenceBridge.lean`, `Asymptotic.lean` |
| Ruzsa base, CRT02 layer, pasting and prime witnesses | `JSP715/CRTBase.lean`, `CRTPattern.lean`, `CRTConstruction.lean`; `CRT.exists_base`, `CRT.layer_ordered`, `CRT.paste_isSumB2`, `CRT.finite_construction` |
| Correct coefficient and subsequence limit | `JSP715/CRTCoefficient.lean`, `CRTAsymptotic.lean`; `CRT.coefficient_eq_floor`, `CRT.ratio_tendsto`, `CRT.conditional_constant_lower` |
| Quantitative comparison and original conclusions | [`JSP715/Main.lean`](https://github.com/CHENLexiao8848/jsp-000715-lean/blob/d202e2c1b904389c6d21f74ab856e3099b0b8391/JSP715/Main.lean#L34); `jsp000715_bounds`, `jsp000715`, `jsp000715_constants_ne` |

## Prior complete proof and precise submitted contribution

The pinned [plby proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos863.lean) at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` already has `Erdos863.erdos_863_bounds`, `Erdos863.erdos_863` and `Erdos863.erdos_863_constants_ne`, with the same conditional quantitative result. It already uses a Ruzsa base and the same CRT02 sparse pattern. Therefore the choice of Ruzsa instead of Singer is a difference from the cited manuscript's presentation, **not an asserted innovation relative to plby**.

The existing fixed [ATTRIBUTION.md](https://github.com/CHENLexiao8848/jsp-000715-lean/blob/d202e2c1b904389c6d21f74ab856e3099b0b8391/ATTRIBUTION.md) discloses that the public plby file was read as proof-route evidence and imported in an earlier local experiment. The selected release uses local modules and does not import or redistribute that third-party file. The distinct work offered for review is the Codex-assisted local implementation, modular interfaces, exact natural/integer transport, integration and reproduction evidence. No mathematical discovery, stronger coefficient, first formalization, wholly unassisted human authorship or independent route discovery is claimed. Any award relevance of those attributable implementation contributions remains unresolved until maintainer assessment.

`CHENLexiao8848` directed the project and maintains/submits the release. Repository ownership and uploading code alone are not authorship evidence; the fixed disclosure and actual source history are supplied for review. The submitter has a direct interest in that review. No independent human verifier is named.

The search on 2026-09-26 also found third-party [#1545](https://github.com/TheJustinSunPrize/awards/pull/1545), which points to this exact SHA. It does not add a separate implementation. Other JSP-ID matches include [#4105](https://github.com/TheJustinSunPrize/awards/pull/4105), [#2885](https://github.com/TheJustinSunPrize/awards/pull/2885), and [#1888](https://github.com/TheJustinSunPrize/awards/pull/1888). Their presence is disclosed without treating PR numbering or opening dates as proof of priority.

## Existing verification evidence and new consistency check

The fixed report records 51 axiom audits and 16 local-module replays, with successful project/component builds and an explicitly disclosed interrupted-run recovery. This review downloaded the exact commit archive and recalculated every entry of `verification/source-sha256.json`: all 23 source/toolchain/manifest/script hashes match. All recorded log paths exist; each of the 16 replay logs identifies its expected target. The three terminal axiom lines are:

```text
'JSP715.jsp000715' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP715.jsp000715_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP715.jsp000715_constants_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is evidence consistency, not a new execution of Lean. Historical build logs show reused artifacts; no clean rebuild follows merely from matching their inputs. Kernel replay uses the Lean kernel against imported dependencies and is not a second independent checker or a clean replay of all Mathlib. A later actual reproduction must be recorded separately with its checked SHA, executed commands, outcomes and limitations. It must not be backfilled as a result of this source-level review.
