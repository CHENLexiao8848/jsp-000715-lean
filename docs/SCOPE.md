# Source-to-theorem map and scope

The [current Erdos 863 question](https://www.erdosproblems.com/863) explicitly starts the comparison with the existence of two square-root asymptotic constants. The formal theorem keeps exactly these premises and proves the comparison for every natural r>=2. It does not add an assumed upper bound, lower bound or construction. The stronger literature sum liminf statement and existence of either limit are separate claims.

| Obligation | Local theorem |
|---|---|
| Sorted sums, diagonal once | `CRT.sumReps`; `CRT.isSumB2_iff_crt02`; `CRTConvention.interval_convention` |
| Positive differences only, exact Nat/Int transport | `DifferenceBridge.card_diffReps_intImage`; `isDiffB2_intImage_iff` |
| Genuine maxima over all admissible subsets of [1,N] | `exists_sumExtremal_set`; `exists_diffExtremal_set` |
| Finite second-moment upper bound | `Difference.diff_card_sq_mul_le_sharp` |
| All-large-N difference epsilon bound | `Difference.diff_card_upper_eventually` |
| Direct finite-field modular Sidon base | `CRT.exists_base` |
| CRT02 Lemma 2.3 exact sparse layer | `CRT.layer_card`; `layer_ordered`; `layer_bound` |
| CRT02 Lemma 2.2 generic pasting | `CRT.paste_isSumB2`; `construction_card`; `construction_subset` |
| Actual finite B2[r] witness, every prime | `CRT.finite_construction` |
| Exact normalization and prime-sequence limit | `CRT.ratio_identity`; `ratio_tendsto`; `coefficient_eq_floor` |
| Unbounded epsilon lower witnesses | `CRT.construction_epsilon_card` |
| Bound on any existing sum constant | `CRT.conditional_constant_lower`; `JSP715.sum_constant_lower` |
| Strict inequality for all r>=2 | `JSP715.sqrt_lt_crtConstant` |
| Full original comparison | `JSP715.jsp000715`; `jsp000715_bounds`; `jsp000715_constants_ne` |

The difference proof applies the Erdos-Turan second-moment argument, with the diagonal contribution M*L and off-diagonal multiplicity bounded by r. Its finite result is M^2*L^2 <= (N+L-1)*(M*L+r*L*(L-1)). The window growth yields the exact leading coefficient sqrt(r). Published/source context is in ATTRIBUTION.md.

For sums, the original CRT02 pattern is range(r) union {r-1+2*j:1<=j<=floor(r/2)}. Its ordered representation count is at most r. Pasting it onto any modular Sidon base fixes the residue pair and injects unordered numerical representations into an ordered layer fiber. The local Ruzsa base is constructed for every prime p (including 2) with modulus p(p-1) and size p-1. Its normalized size tends to one, giving exactly (r+floor(r/2))/sqrt(r+2*floor(r/2)).

For any assumed full limit of the normalized sum extremum, restricting to this unbounded prime-modulus sequence has the same limit. This is why the explicit unbounded-N construction proves the full conditional constant comparison without requiring prime-gap estimates. The unconditional unbounded strict-extremum corollary is stated separately, with its own precise quantifiers.
