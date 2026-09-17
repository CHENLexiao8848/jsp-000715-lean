import JSP715.Basic
import JSP715.Comparison
import JSP715.Asymptotic
import JSP715.SumAsymptotic

namespace JSP715

/-- Independent finite Erdős–Turán estimate, transported from integer sets. -/
theorem difference_finite_upper {N m r : ℕ} (hm : 0 < m) (A : Finset ℕ)
    (hDiff : IsDiffB2 r A) (hA : A ⊆ Finset.Icc 1 N) :
    (A.card ^ 2 : ℝ) ≤ (N + m : ℝ) * (A.card / m + r) := by
  have h := Difference.diff_card_sq_le hm
    (DifferenceBridge.subset_intImage hA)
    ((DifferenceBridge.isDiffB2_intImage_iff r A).mpr hDiff)
  simpa only [DifferenceBridge.card_intImage] using h

/-- The exact finite CRT layer construction with a proved Ruzsa modular base. -/
theorem sum_finite_lower {r p : ℕ} (hr : 1 ≤ r) (hp : p.Prime) :
    (p - 1) * (r + r / 2) ≤
      sumExtremal r (p * (p - 1) * (r + 2 * (r / 2))) :=
  CRT.extremal_special_lower hr hp

theorem difference_constant_upper {r : ℕ} {c : ℝ}
    (hc : HasSqrtAsymptotic (diffExtremal r) c) : c ≤ Real.sqrt r := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact le_of_tendsto hc ((diff_upper_eventually r hε).mono fun _ h => h.le)

theorem sum_constant_lower {r : ℕ} (hr : 2 ≤ r) {c : ℝ}
    (hc : HasSqrtAsymptotic (sumExtremal r) c) : crtConstant r ≤ c :=
  CRT.conditional_constant_lower hr hc

/-- JSP-000715 / Erdős 863: both bounds are proved; only the original
asymptotic-constant existence hypotheses are assumed. -/
theorem jsp000715_bounds {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ}
    (hsum : HasSqrtAsymptotic (sumExtremal r) cSum)
    (hdiff : HasSqrtAsymptotic (diffExtremal r) cDiff) :
    cDiff ≤ Real.sqrt r ∧ Real.sqrt r < crtConstant r ∧ crtConstant r ≤ cSum :=
  ⟨difference_constant_upper hdiff, sqrt_lt_crtConstant hr, sum_constant_lower hr hsum⟩

theorem jsp000715 {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ}
    (hsum : HasSqrtAsymptotic (sumExtremal r) cSum)
    (hdiff : HasSqrtAsymptotic (diffExtremal r) cDiff) : cDiff < cSum := by
  obtain ⟨hu, hs, hl⟩ := jsp000715_bounds hr hsum hdiff
  exact hu.trans_lt (hs.trans_le hl)

theorem jsp000715_constants_ne {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ}
    (hsum : HasSqrtAsymptotic (sumExtremal r) cSum)
    (hdiff : HasSqrtAsymptotic (diffExtremal r) cDiff) : cSum ≠ cDiff :=
  ne_of_gt (jsp000715 hr hsum hdiff)

/-- Without assuming either limit exists, the sum extremal value is strictly
larger than the difference extremal value for unbounded ambient lengths. -/
theorem jsp000715_unbounded_strict {r : ℕ} (hr : 2 ≤ r) (N₀ : ℕ) :
    ∃ N ≥ N₀, diffExtremal r N < sumExtremal r N := by
  let ε := (crtConstant r - Real.sqrt r) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith [sqrt_lt_crtConstant hr]
  obtain ⟨K, hK⟩ := diff_upper_epsilon r hε
  obtain ⟨N, hN, hsum⟩ := sum_lower_epsilon hr hε (max N₀ (max K 1))
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hNK : K ≤ N := (le_max_left K 1).trans ((le_max_right _ _).trans hN)
  have hNpos : 0 < N := by omega
  have hdiff := hK N hNK
  have hgap : Real.sqrt r + ε < crtConstant r - ε := by
    dsimp [ε]; linarith [sqrt_lt_crtConstant hr]
  have hquot := hdiff.trans (hgap.trans hsum)
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have hcard : (diffExtremal r N : ℝ) < (sumExtremal r N : ℝ) :=
    (div_lt_div_iff_of_pos_right hsqrt).mp hquot
  exact ⟨N, hN₀, by exact_mod_cast hcard⟩

end JSP715
