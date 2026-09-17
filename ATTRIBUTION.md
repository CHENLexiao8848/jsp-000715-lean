# Attribution and provenance

## Mathematical result

The canonical awards entry credits **Boon Suan Ho and GPT-5.4 Pro**, by deduction from existing literature. This submission does not request a mathematical-solver change. It uses the following mathematical sources:

- P. Erdos, *Some of my forgotten problems in number theory*, Hardy-Ramanujan Journal 15 (1992), pp.39-40, [DOI](https://doi.org/10.46298/hrj.1992.125); current precise [Erdos Problem 863](https://www.erdosproblems.com/863).
- B. S. Ho, *On a problem of Erdos, Berend, and Freud concerning bounded sums and bounded differences*, [public exposition](https://boonsuan.github.io/erdos863.pdf), especially the conditional comparison in Corollary 1.
- J. Cilleruelo, I. Z. Ruzsa and C. Trujillo, *Upper and Lower Bounds for Finite B_h[g] Sequences*, Journal of Number Theory 97 (2002), 26-34, [DOI](https://doi.org/10.1006/jnth.2001.2767), [author manuscript](https://matematicas.uam.es/~franciscojavier.cilleruelo/Papers/bh.pdf): Theorem 2.1, Lemmas 2.2 and 2.3 in the manuscript.
- The Erdos-Turan second-moment method for the difference bound; W. Xu, *Popular differences and generalized Sidon sets*, Journal of Number Theory 186 (2018), 103-120, Theorem 3.1, [DOI](https://doi.org/10.1016/j.jnt.2017.09.016), [arXiv](https://arxiv.org/abs/1706.05969).

## This Lean implementation and contributor roles

- **Formalization:** Codex-assisted local development directed by **[CHENLexiao8848](https://github.com/CHENLexiao8848)**. Codex generated the independent local B/C Lean implementation, the Nat/Int bridge, the common extremal interfaces and integration, and executed the recorded checks. This is an explicit AI-assistance disclosure, not a claim that the account holder personally wrote every proof term.
- **Repository owner / submitter / project direction:** CHENLexiao8848 commissioned and directed the local formalization and authorized review, publication and the catalog evidence submission. No original mathematical-solver credit or first-formalization priority is claimed.
- **Verification:** the recorded Lean compiler, axiom audits and Lean-kernel replays were executed in the local development workflow. They are machine checks; no independent human referee endorsement is claimed.

Concrete contributions are the parameterized difference-energy proof (`DifferenceUpper`); original CRT02 sparse layer and generic pasting with a proved finite-field Ruzsa base (`CRTBase`, `CRTPattern`, `CRTConstruction`); exact coefficient and asymptotic interfaces; exact natural/integer representation transport (`DifferenceBridge`); and the complete terminal comparison (`Main`).

## Prior public formalization

An earlier complete formal proof was found at [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos863.lean), commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Its header credits the informal authors and Codex / GPT-5.6 Sol for earlier formal work. Existing [awards issue #19](https://github.com/TheJustinSunPrize/awards/issues/19) remains acknowledged. This repository is additional local implementation and integration evidence, not a first solution.

The public file was read as proof-route evidence; a prior local replay experiment imported it. The current implementation uses newly written local proof modules and does not import or redistribute that third-party file. No broad redistribution license for that file was established, and none is assumed or granted here. The earlier replay experiment, downloaded papers and their logs are excluded.

Mathlib is obtained at its pinned public commit and remains under its [Apache-2.0 license](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/LICENSE). This repository does not redistribute Mathlib or change any third-party license.
