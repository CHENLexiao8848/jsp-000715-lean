import JSP715.CRTConstruction
import JSP715.CRTCoefficient

namespace JSP715.CRT

open Filter

noncomputable section

/-- Ambient length of the prime-indexed CRT02 construction. -/
def ambient (r n : ℕ) : ℕ :=
  primes n * (primes n - 1) * (r + 2 * (r / 2))

lemma ambient_pos {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 0 < ambient r n := by
  have hp := (primes_prime n).two_le
  unfold ambient
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

/-- Prime-indexed ambient lengths are unbounded; no prime-gap estimate is used. -/
lemma ambient_tendsto {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (ambient r) atTop atTop := by
  refine tendsto_atTop_mono' atTop (Eventually.of_forall fun n => ?_) primes_tendsto
  have hp := (primes_prime n).two_le
  unfold ambient
  exact (Nat.le_mul_of_pos_right _ (by omega : 0 < primes n - 1)).trans
    (Nat.le_mul_of_pos_right _ (by omega : 0 < r + 2 * (r / 2)))

/-- Exact epsilon interface for actual sets at arbitrarily large ambient lengths.
This does not assert an all-large-length lower bound or existence of a limit. -/
theorem construction_epsilon {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε)
    (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧ ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ IsSumB2 r A ∧
      coefficient r - ε < (A.card : ℝ) / Real.sqrt N := by
  have hlarge : ∀ᶠ n in atTop, N₀ ≤ ambient r n :=
    (ambient_tendsto (by omega : 1 ≤ r)).eventually (eventually_ge_atTop N₀)
  have hclose := (ratio_tendsto hr).eventually_const_lt
    (show coefficient r - ε < coefficient r by linarith)
  obtain ⟨n, hn, hbound⟩ := (hlarge.and hclose).exists
  obtain ⟨A, hA, hB, hcard⟩ := finite_construction (by omega : 1 ≤ r) (primes_prime n)
  refine ⟨ambient r n, hn, ambient_pos (by omega) n, A, hA, hB, ?_⟩
  simpa only [hcard, ambient] using hbound

/-- Maximum cardinality of a CRT02-convention `B₂[r]` subset of `[1,N]`.
The finite supremum is over actual admissible subsets of the interval. -/
def sumExtremal (r N : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 N).powerset).filter (IsSumB2 r)).sup Finset.card

lemma card_le_extremal {r N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hB : IsSumB2 r A) :
    A.card ≤ sumExtremal r N := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hB⟩)

/-- The finite supremum is attained by an admissible set, including at `N=0`. -/
theorem exists_extremal (r N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSumB2 r A ∧
      A.card = sumExtremal r N := by
  classical
  let admissible := ((Finset.Icc 1 N).powerset).filter (IsSumB2 r)
  have hzero : (∅ : Finset ℕ) ∈ admissible := by
    simp [admissible, IsSumB2, sumReps]
  obtain ⟨A, hA, hcard⟩ :=
    Finset.exists_mem_eq_sup admissible ⟨∅, hzero⟩ Finset.card
  obtain ⟨hsub, hB⟩ := Finset.mem_filter.mp hA
  exact ⟨A, Finset.mem_powerset.mp hsub, hB, hcard.symm⟩

lemma extremal_mono (r : ℕ) : Monotone (sumExtremal r) := by
  intro M N hMN
  obtain ⟨A, hA, hB, hcard⟩ := exists_extremal r M
  rw [← hcard]
  apply card_le_extremal (hB := hB)
  intro a ha
  obtain ⟨ha1, haM⟩ := Finset.mem_Icc.mp (hA ha)
  exact Finset.mem_Icc.mpr ⟨ha1, haM.trans hMN⟩

lemma extremal_special_lower {r p : ℕ} (hr : 1 ≤ r) (hp : p.Prime) :
    (p - 1) * (r + r / 2) ≤
      sumExtremal r (p * (p - 1) * (r + 2 * (r / 2))) := by
  obtain ⟨A, hA, hB, hcard⟩ := finite_construction hr hp
  rw [← hcard]
  exact card_le_extremal hA hB

/-- The extremal function attains every coefficient below CRT02's coefficient
at arbitrarily large positive ambient lengths. -/
theorem extremal_epsilon {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε)
    (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧
      coefficient r - ε < (sumExtremal r N : ℝ) / Real.sqrt N := by
  obtain ⟨N, hN, hpos, A, hA, hB, hbound⟩ := construction_epsilon hr hε N₀
  refine ⟨N, hN, hpos, hbound.trans_le ?_⟩
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact_mod_cast card_le_extremal hA hB

/-- Integration interface for any extremal function dominating all admissible
cardinalities. Only the displayed convergence assumption is needed. -/
theorem constant_lower_of_dominates {r : ℕ} (hr : 2 ≤ r) {f : ℕ → ℝ} {c : ℝ}
    (hdom : ∀ N (A : Finset ℕ), A ⊆ Finset.Icc 1 N → IsSumB2 r A →
      (A.card : ℝ) ≤ f N)
    (hc : Tendsto (fun N : ℕ => f N / Real.sqrt N) atTop (nhds c)) :
    coefficient r ≤ c := by
  apply le_of_tendsto_of_tendsto' (ratio_tendsto hr)
    (hc.comp (ambient_tendsto (by omega : 1 ≤ r)))
  intro n
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  obtain ⟨A, hA, hB, hcard⟩ := finite_construction (by omega : 1 ≤ r) (primes_prime n)
  rw [← hcard]
  exact hdom (ambient r n) A hA hB

/-- If the normalized extremal function has a full limit, CRT02's exact
coefficient is a lower bound for it. Limit existence remains a hypothesis. -/
theorem conditional_constant_lower {r : ℕ} (hr : 2 ≤ r) {c : ℝ}
    (hc : Tendsto (fun N : ℕ => (sumExtremal r N : ℝ) / Real.sqrt N)
      atTop (nhds c)) :
    coefficient r ≤ c := by
  apply constant_lower_of_dominates hr (hc := hc)
  intro N A hA hB
  exact_mod_cast card_le_extremal hA hB

end

end JSP715.CRT
