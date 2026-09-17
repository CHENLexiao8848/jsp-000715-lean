import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The bounded-positive-difference Erdős–Turán estimate

Independent formalization of the local second-moment argument in Section 3 of
Boon Suan Ho, `On a problem of Erdős, Berend, and Freud concerning bounded sums
and bounded differences`. Integer subtraction records signed differences exactly.
-/

open Finset
open scoped BigOperators Pointwise

namespace JSP715.Difference

/-- Ordered representations of the integer difference `d`. -/
def diffReps (A : Finset ℤ) (d : ℤ) : Finset (ℤ × ℤ) :=
  (A ×ˢ A).filter fun p => p.1 - p.2 = d

/-- Every strictly positive difference has at most `r` ordered representations. -/
def IsDiffB2 (r : ℕ) (A : Finset ℤ) : Prop :=
  ∀ d : ℤ, 0 < d → (diffReps A d).card ≤ r

theorem mem_diffReps {A : Finset ℤ} {d a b : ℤ} :
    (a, b) ∈ diffReps A d ↔ a ∈ A ∧ b ∈ A ∧ a - b = d := by
  simp [diffReps, and_assoc]

theorem mem_diffReps_pos {A : Finset ℤ} {d a b : ℤ} (hd : 0 < d) :
    (a, b) ∈ diffReps A d ↔ a ∈ A ∧ b ∈ A ∧ b < a ∧ a - b = d := by
  rw [mem_diffReps]
  constructor
  · rintro ⟨ha, hb, he⟩
    exact ⟨ha, hb, by omega, he⟩
  · rintro ⟨ha, hb, _, he⟩
    exact ⟨ha, hb, he⟩

theorem diffReps_neg_card (A : Finset ℤ) (d : ℤ) :
    (diffReps A (-d)).card = (diffReps A d).card := by
  apply Finset.card_equiv (Equiv.prodComm ℤ ℤ)
  rintro ⟨a, b⟩
  simp only [diffReps, mem_filter, mem_product, Equiv.prodComm_apply, Prod.swap_prod_mk]
  constructor <;> rintro ⟨⟨ha, hb⟩, he⟩ <;> exact ⟨⟨hb, ha⟩, by omega⟩

theorem IsDiffB2.nonzero {r : ℕ} {A : Finset ℤ} (h : IsDiffB2 r A)
    {d : ℤ} (hd : d ≠ 0) : (diffReps A d).card ≤ r := by
  rcases lt_or_gt_of_ne hd with hn | hp
  · have ht := h (-d) (by omega)
    rwa [diffReps_neg_card] at ht
  · exact h d hp

/-- Equivalence with the usual condition on every nonzero signed difference. -/
theorem isDiffB2_iff_nonzero {r : ℕ} {A : Finset ℤ} :
    IsDiffB2 r A ↔ ∀ d : ℤ, d ≠ 0 → (diffReps A d).card ≤ r := by
  exact ⟨fun h _ hd => h.nonzero hd, fun h d hd => h d (ne_of_gt hd)⟩

/-- On positive differences, integer and natural subtraction agree. -/
theorem nat_difference_iff {a b d : ℕ} (hd : 0 < d) :
    (a : ℤ) - (b : ℤ) = (d : ℤ) ↔ b < a ∧ a - b = d := by
  omega

private theorem collision_diagonal (A : Finset ℤ) (i : ℤ) :
    ((A ×ˢ A).filter fun p => p.1 + i = p.2 + i).card = A.card := by
  have he : ((A ×ˢ A).filter fun p => p.1 + i = p.2 + i) = A.diag := by
    ext p
    simp only [mem_filter, mem_product, add_left_inj, Finset.mem_diag]
    aesop
  rw [he, Finset.diag_card]

private theorem collision_le {r : ℕ} {A : Finset ℤ} (h : IsDiffB2 r A)
    (i j : ℤ) :
    ((A ×ˢ A).filter fun p => p.1 + i = p.2 + j).card ≤
      if i = j then A.card else r := by
  split_ifs with hij
  · subst j
    exact (collision_diagonal A i).le
  · have he : ((A ×ˢ A).filter fun p => p.1 + i = p.2 + j) =
        diffReps A (j - i) := by
      ext p
      simp only [diffReps, mem_filter]
      constructor <;> rintro ⟨hp, he⟩ <;> exact ⟨hp, by omega⟩
    rw [he]
    exact h.nonzero (by omega)

/-- The second moment counts collisions between each pair of translates. -/
theorem energy_eq_sum_collisions (A T : Finset ℤ) :
    A.addEnergy T = ∑ i ∈ T, ∑ j ∈ T,
      ((A ×ˢ A).filter fun p => p.1 + i = p.2 + j).card := by
  rw [Finset.addEnergy_comm]
  simp only [Finset.addEnergy, Finset.card_filter, Finset.sum_product]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  simp only [add_comm]

/-- Exact diagonal/off-diagonal second-moment bound for distinct translates. -/
theorem energy_le_sharp {r : ℕ} {A : Finset ℤ} (h : IsDiffB2 r A) (T : Finset ℤ) :
    A.addEnergy T ≤ A.card * T.card + r * T.card * (T.card - 1) := by
  rw [energy_eq_sum_collisions]
  calc
    _ ≤ ∑ i ∈ T, ∑ j ∈ T, if i = j then A.card else r := by
      exact sum_le_sum fun i _ => sum_le_sum fun j _ => collision_le h i j
    _ = ∑ _i ∈ T, (A.card + r * (T.card - 1)) := by
      apply sum_congr rfl
      intro i hi
      simp [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, hi,
        Finset.card_erase_of_mem, mul_comm]
    _ = _ := by simp [mul_add, mul_comm, mul_left_comm, mul_assoc]

/-- A convenient relaxation of the exact second-moment bound. -/
theorem energy_le {r : ℕ} {A : Finset ℤ} (h : IsDiffB2 r A) (T : Finset ℤ) :
    A.addEnergy T ≤ A.card * T.card + r * T.card ^ 2 := by
  rw [energy_eq_sum_collisions]
  calc
    _ ≤ ∑ i ∈ T, ∑ j ∈ T, ((if i = j then A.card else 0) + r) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      exact (collision_le h i j).trans (by split_ifs <;> omega)
    _ = _ := by
      simp only [sum_add_distrib, Finset.sum_ite_eq, sum_const, nsmul_eq_mul]
      simp only [Finset.sum_ite_of_true (fun _ hi => hi)]
      simp
      ring

/-- Finite Erdős–Turán inequality before division; valid also for `L = 0`. -/
theorem diff_card_sq_mul_le {r N L : ℕ} {A : Finset ℤ}
    (hA : A ⊆ Icc 1 (N : ℤ)) (h : IsDiffB2 r A) :
    A.card ^ 2 * L ^ 2 ≤ (N + L) * (A.card * L + r * L ^ 2) := by
  let T : Finset ℤ := Ico 0 (L : ℤ)
  let U : Finset ℤ := Icc 1 ((N : ℤ) + L)
  have hT : T.card = L := by simp [T, Int.card_Ico]
  have hU : U.card = N + L := by
    simp only [U, Int.card_Icc]
    omega
  have hf : ((A ×ˢ T).filter fun p => p.1 + p.2 ∈ U) = A ×ˢ T := by
    apply filter_eq_self.mpr
    intro p hp
    obtain ⟨ha, ht⟩ := mem_product.mp hp
    have ha' := mem_Icc.mp (hA ha)
    have ht' := mem_Ico.mp ht
    apply mem_Icc.mpr
    omega
  have hc := Finset.card_sq_le_card_mul_addEnergy A T U
  rw [hf, card_product, mul_pow, hT, hU] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (by simpa [hT] using energy_le h T))

/-- The precise finite window inequality, including both endpoint corrections. -/
theorem diff_card_sq_mul_le_sharp {r N L : ℕ} {A : Finset ℤ}
    (hA : A ⊆ Icc 1 (N : ℤ)) (h : IsDiffB2 r A) :
    A.card ^ 2 * L ^ 2 ≤ (N + L - 1) * (A.card * L + r * L * (L - 1)) := by
  let T : Finset ℤ := Ico 0 (L : ℤ)
  let U : Finset ℤ := Ico 1 ((N : ℤ) + L)
  have hT : T.card = L := by simp [T, Int.card_Ico]
  have hU : U.card = N + L - 1 := by
    simp only [U, Int.card_Ico]
    omega
  have hf : ((A ×ˢ T).filter fun p => p.1 + p.2 ∈ U) = A ×ˢ T := by
    apply filter_eq_self.mpr
    intro p hp
    obtain ⟨ha, ht⟩ := mem_product.mp hp
    have ha' := mem_Icc.mp (hA ha)
    have ht' := mem_Ico.mp ht
    apply mem_Ico.mpr
    omega
  have hc := Finset.card_sq_le_card_mul_addEnergy A T U
  rw [hf, card_product, mul_pow, hT, hU] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (by simpa [hT] using energy_le_sharp h T))

open Filter

/-- A real-valued interface without natural subtraction or hidden endpoint conditions. -/
theorem diff_card_sq_le {r N L : ℕ} {A : Finset ℤ} (hL : 0 < L)
    (hA : A ⊆ Icc 1 (N : ℤ)) (h : IsDiffB2 r A) :
    (A.card : ℝ) ^ 2 ≤ ((N : ℝ) + L) * ((A.card : ℝ) / L + r) := by
  have hc : (A.card : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤
      ((N : ℝ) + L) * ((A.card : ℝ) * L + r * (L : ℝ) ^ 2) := by
    exact_mod_cast diff_card_sq_mul_le hA h
  have hp : (0 : ℝ) < L := by exact_mod_cast hL
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hp)).mp
  calc
    _ ≤ ((N : ℝ) + L) * ((A.card : ℝ) * L + r * (L : ℝ) ^ 2) := by
      simpa [mul_comm] using hc
    _ = _ := by field_simp

/-- Normalized finite estimate whose error terms can be sent to zero independently. -/
theorem diff_normalized_sq_le {r N L : ℕ} {A : Finset ℤ} (hN : 0 < N)
    (hL : 0 < L) (hA : A ⊆ Icc 1 (N : ℤ)) (h : IsDiffB2 r A) :
    ((A.card : ℝ) / Real.sqrt N) ^ 2 ≤
      (Real.sqrt N / L + 1 / Real.sqrt N) * ((A.card : ℝ) / Real.sqrt N) +
      r * (1 + (L : ℝ) / N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hl : (0 : ℝ) < L := by exact_mod_cast hL
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have he : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hn.le
  have hc := div_le_div_of_nonneg_right (diff_card_sq_le hL hA h) hn.le
  convert hc using 1
  · rw [div_pow, he]
  · field_simp
    rw [he]
    ring

private theorem quadratic_le {x b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : x ^ 2 ≤ b * x + c) : x ≤ b + Real.sqrt c := by
  have hs := Real.sq_sqrt hc
  have hn := Real.sqrt_nonneg c
  by_contra! hx
  nlinarith [mul_nonneg hb hn, mul_pos (sub_pos.mpr hx) (show 0 < x by linarith)]

/-- A ceiling avoids subtracting one in the auxiliary-length estimates. -/
noncomputable def windowLength (N : ℕ) : ℕ := ⌈(N : ℝ) ^ (3 / 4 : ℝ)⌉₊

private theorem power_quarter_limit :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (- (1 / 4 : ℝ))) atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

private theorem power_ratio_limit :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 4 : ℝ) / N) atTop (nhds 0) := by
  apply power_quarter_limit.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ = (N : ℝ) ^ ((3 / 4 : ℝ) - 1) := by norm_num
    _ = _ := by rw [Real.rpow_sub hn, Real.rpow_one]

private theorem sqrt_power_ratio_limit :
    Tendsto (fun N : ℕ => Real.sqrt N / (N : ℝ) ^ (3 / 4 : ℝ)) atTop (nhds 0) := by
  apply power_quarter_limit.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub (by exact_mod_cast hN : (0 : ℝ) < N)]
  norm_num

private theorem window_power_ratio_limit :
    Tendsto (fun N : ℕ => (windowLength N : ℝ) / (N : ℝ) ^ (3 / 4 : ℝ))
      atTop (nhds 1) :=
  tendsto_nat_ceil_div_atTop.comp
    ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)

theorem windowLength_div_tendsto_zero :
    Tendsto (fun N : ℕ => (windowLength N : ℝ) / N) atTop (nhds 0) := by
  have ht := window_power_ratio_limit.mul power_ratio_limit
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hp : (N : ℝ) ^ (3 / 4 : ℝ) ≠ 0 := by positivity
  field_simp

theorem sqrt_div_windowLength_tendsto_zero :
    Tendsto (fun N : ℕ => Real.sqrt N / (windowLength N : ℝ)) atTop (nhds 0) := by
  have ht := sqrt_power_ratio_limit.div window_power_ratio_limit (by norm_num)
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hp : (N : ℝ) ^ (3 / 4 : ℝ) ≠ 0 := by positivity
  dsimp
  field_simp

/-- Uniform majorant for the normalized cardinality. -/
noncomputable def diffMajorant (r N : ℕ) : ℝ :=
  (Real.sqrt N / windowLength N + 1 / Real.sqrt N) +
    Real.sqrt (r * (1 + (windowLength N : ℝ) / N))

theorem diffMajorant_tendsto (r : ℕ) :
    Tendsto (diffMajorant r) atTop (nhds (Real.sqrt r)) := by
  change Tendsto (fun N : ℕ => (Real.sqrt N / windowLength N + 1 / Real.sqrt N) +
    Real.sqrt ((r : ℝ) * (1 + (windowLength N : ℝ) / N))) atTop (nhds (Real.sqrt r))
  have hi : Tendsto (fun N : ℕ => 1 / Real.sqrt (N : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, one_div] using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  have hb := sqrt_div_windowLength_tendsto_zero.add hi
  have hc : Tendsto (fun N : ℕ => Real.sqrt ((r : ℝ) *
      (1 + (windowLength N : ℝ) / N))) atTop (nhds (Real.sqrt ((r : ℝ) * (1 + 0)))) :=
    (tendsto_const_nhds.mul
      (tendsto_const_nhds.add windowLength_div_tendsto_zero)).sqrt
  simpa only [add_zero, zero_add, mul_one] using hb.add hc

theorem diff_card_div_sqrt_le {r N : ℕ} {A : Finset ℤ} (hN : 0 < N)
    (hA : A ⊆ Icc 1 (N : ℤ)) (h : IsDiffB2 r A) :
    (A.card : ℝ) / Real.sqrt N ≤ diffMajorant r N := by
  have hl : 0 < windowLength N := by
    apply Nat.ceil_pos.mpr
    positivity
  exact quadratic_le (by positivity) (by positivity)
    (diff_normalized_sq_le hN hl hA h)

/-- The uniform, unconditional sharp-leading-constant upper bound, for every `r`. -/
theorem diff_card_upper_eventually (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℤ,
      A ⊆ Icc 1 (N : ℤ) → IsDiffB2 r A →
      (A.card : ℝ) ≤ (Real.sqrt r + ε) * Real.sqrt N := by
  have hm : ∀ᶠ N : ℕ in atTop, diffMajorant r N < Real.sqrt r + ε :=
    (diffMajorant_tendsto r).eventually (gt_mem_nhds (by linarith))
  obtain ⟨N₀, hn⟩ := eventually_atTop.mp (hm.and (eventually_gt_atTop 0))
  refine ⟨N₀, fun N hN A hA h => ?_⟩
  obtain ⟨hmN, hpN⟩ := hn N hN
  have hb := (diff_card_div_sqrt_le hpN hA h).trans hmN.le
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hpN))).mp hb

end JSP715.Difference
