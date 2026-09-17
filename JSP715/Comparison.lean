import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace JSP715

/-- The Cilleruelo–Ruzsa–Trujillo lower-bound coefficient, with natural division. -/
noncomputable def crtConstant (r : ℕ) : ℝ :=
  ((r + r / 2 : ℕ) : ℝ) / Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ)

/-- The strict numerical separation for every parameter in the prize question. -/
theorem sqrt_lt_crtConstant {r : ℕ} (hr : 2 ≤ r) :
    Real.sqrt r < crtConstant r := by
  have ht : (0 : ℝ) < (r / 2 : ℕ) := by
    exact_mod_cast (show 0 < r / 2 by omega)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hD : (0 : ℝ) < (r : ℝ) + 2 * (r / 2 : ℕ) := by positivity
  unfold crtConstant
  push_cast
  rw [lt_div_iff₀ (Real.sqrt_pos.mpr hD), ← Real.sqrt_mul hr0]
  apply (Real.sqrt_lt (by positivity) (by positivity)).mpr
  nlinarith [sq_pos_of_pos ht]

end JSP715
