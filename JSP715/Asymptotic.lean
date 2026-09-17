import JSP715.Basic

namespace JSP715

open Filter

/-- Uniform upper bound on the normalized difference extremal function. -/
theorem diff_upper_eventually (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (diffExtremal r N : ℝ) / Real.sqrt N < Real.sqrt r + ε := by
  obtain ⟨N₀, hN₀⟩ := DifferenceBridge.nat_diff_upper_eventually r
    (show 0 < ε / 2 by linarith)
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop 0] with N hN hpos
  obtain ⟨A, hA, hDiff, hcard⟩ := exists_diffExtremal_set r N
  have hbound := hN₀ N hN A hA hDiff
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hpos)
  rw [← hcard]
  exact ((div_le_iff₀ hsqrt).mpr hbound).trans_lt (by linarith)

theorem diff_upper_epsilon (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (diffExtremal r N : ℝ) / Real.sqrt N < Real.sqrt r + ε :=
  eventually_atTop.mp (diff_upper_eventually r hε)

theorem diff_limsup_upper (r : ℕ) :
    Filter.limsup (fun N : ℕ =>
      (diffExtremal r N : ℝ) / Real.sqrt N) atTop ≤ Real.sqrt r := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  apply Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le atTop (x := (0 : ℝ))
      (fun _ => by positivity))
  exact (diff_upper_eventually r hε).mono fun _ h => h.le

end JSP715
