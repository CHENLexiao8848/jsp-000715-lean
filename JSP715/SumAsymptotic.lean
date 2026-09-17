import JSP715.Basic
import JSP715.Comparison

namespace JSP715

/-- The independent CRT construction supplies unbounded ambient witnesses. -/
theorem sum_lower_epsilon {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε)
    (N₀ : ℕ) :
    ∃ N ≥ N₀, crtConstant r - ε < (sumExtremal r N : ℝ) / Real.sqrt N := by
  obtain ⟨N, hN, _, hbound⟩ := CRT.extremal_epsilon hr hε N₀
  exact ⟨N, hN, hbound⟩

end JSP715
