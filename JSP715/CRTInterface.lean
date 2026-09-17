import JSP715.CRTAsymptotic
import JSP715.CRTConvention
import Mathlib.Algebra.Order.Floor.Semifield

namespace JSP715.CRT

/-- The user-facing predicate is exactly CRT02's positive-integer, unordered convention. -/
theorem isSumB2_iff_crt02 {r N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) :
    IsSumB2 r A ↔ ∀ s : ℤ, 0 < s →
      (CRTConvention.integerSumReps A s).card ≤ r := by
  exact CRTConvention.interval_convention r N hA

/-- Natural division in the parameter really is the floor in the paper. -/
theorem half_eq_floor (r : ℕ) : r / 2 = ⌊(r : ℝ) / 2⌋₊ :=
  (Nat.floor_div_eq_div r 2).symm

/-- The numerical coefficient, written with the paper's real floor notation. -/
theorem coefficient_eq_floor (r : ℕ) :
    coefficient r =
      ((r : ℝ) + (⌊(r : ℝ) / 2⌋₊ : ℝ)) /
        Real.sqrt ((r : ℝ) + 2 * (⌊(r : ℝ) / 2⌋₊ : ℝ)) := by
  rw [← half_eq_floor]
  simp only [coefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

/-- Division-free epsilon interface with an actual finite constructed set. -/
theorem construction_epsilon_card {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε)
    (N₀ : ℕ) :
    ∃ N ≥ N₀, ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSumB2 r A ∧
      (coefficient r - ε) * Real.sqrt N < (A.card : ℝ) := by
  obtain ⟨N, hN, hpos, A, hA, hB, hratio⟩ := construction_epsilon hr hε N₀
  refine ⟨N, hN, A, hA, hB, ?_⟩
  exact (lt_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hpos))).mp hratio

end JSP715.CRT
