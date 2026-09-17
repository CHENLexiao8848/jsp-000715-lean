import JSP715.CRTInterface
import JSP715.DifferenceBridge

/-! Common natural-number interfaces, supplied by the independently proved B/C modules. -/
namespace JSP715

abbrev sumReps := CRT.sumReps
abbrev diffReps := DifferenceBridge.natDiffReps
abbrev IsSumB2 := CRT.IsSumB2
abbrev IsDiffB2 := DifferenceBridge.IsNatDiffB2
noncomputable abbrev sumExtremal := CRT.sumExtremal

/-- Maximum cardinality over all admissible positive-difference subsets of `[1,N]`. -/
noncomputable def diffExtremal (r N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).powerset.filter (IsDiffB2 r)).sup Finset.card

/-- The asymptotic-constant hypothesis stated in the original question. -/
def HasSqrtAsymptotic (f : ℕ → ℕ) (c : ℝ) : Prop :=
  Filter.Tendsto (fun N : ℕ => (f N : ℝ) / Real.sqrt N) Filter.atTop (nhds c)

@[simp] theorem mem_sumReps {A : Finset ℕ} {a b n : ℕ} :
    (a, b) ∈ sumReps A n ↔ a ∈ A ∧ b ∈ A ∧ a ≤ b ∧ a + b = n := by
  simp [sumReps, CRT.sumReps, and_assoc]

@[simp] theorem diagonal_mem_sumReps {A : Finset ℕ} {a : ℕ} :
    (a, a) ∈ sumReps A (a + a) ↔ a ∈ A := by simp

def integerDiffReps (A : Finset ℕ) (d : ℤ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p => (p.1 : ℤ) - p.2 = d

theorem positive_nat_sub_iff {a b d : ℕ} (hd : 0 < d) :
    a - b = d ↔ (a : ℤ) - b = (d : ℤ) := by omega

theorem diffReps_eq_integerDiffReps {A : Finset ℕ} {d : ℕ} (hd : 0 < d) :
    diffReps A d = integerDiffReps A d := by
  ext p
  simp only [diffReps, DifferenceBridge.natDiffReps, integerDiffReps, Finset.mem_filter]
  rw [positive_nat_sub_iff hd]

theorem mem_diffReps_iff {A : Finset ℕ} {a b d : ℕ} (hd : 0 < d) :
    (a, b) ∈ diffReps A d ↔
      a ∈ A ∧ b ∈ A ∧ b < a ∧ (a : ℤ) - b = (d : ℤ) := by
  simp only [diffReps, DifferenceBridge.natDiffReps, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    exact ⟨ha, hb, by omega, (positive_nat_sub_iff hd).mp hab⟩
  · rintro ⟨ha, hb, _, hab⟩
    exact ⟨⟨ha, hb⟩, (positive_nat_sub_iff hd).mpr hab⟩

theorem isDiffB2_iff_integer (r : ℕ) (A : Finset ℕ) :
    IsDiffB2 r A ↔ ∀ d : ℤ, 0 < d → (integerDiffReps A d).card ≤ r := by
  constructor
  · intro h d hd
    have hdNat : 0 < d.toNat := by omega
    have hdCast : (d.toNat : ℤ) = d := by omega
    simpa [diffReps_eq_integerDiffReps hdNat, hdCast] using h d.toNat hdNat
  · intro h d hd
    change (diffReps A d).card ≤ r
    rw [diffReps_eq_integerDiffReps hd]
    exact h d (by exact_mod_cast hd)

theorem exists_sumExtremal_set (r N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSumB2 r A ∧
      A.card = sumExtremal r N := CRT.exists_extremal r N

theorem exists_diffExtremal_set (r N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsDiffB2 r A ∧
      A.card = diffExtremal r N := by
  classical
  let F := (Finset.Icc 1 N).powerset.filter (IsDiffB2 r)
  have he : (∅ : Finset ℕ) ∈ F := by
    simp [F, IsDiffB2, DifferenceBridge.IsNatDiffB2, DifferenceBridge.natDiffReps]
  obtain ⟨A, hA, hcard⟩ := Finset.exists_mem_eq_sup F ⟨∅, he⟩ Finset.card
  exact ⟨A, Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1,
    (Finset.mem_filter.mp hA).2, hcard.symm⟩

theorem card_le_sumExtremal {r N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hSum : IsSumB2 r A) :
    A.card ≤ sumExtremal r N := CRT.card_le_extremal hA hSum

theorem card_le_diffExtremal {r N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hDiff : IsDiffB2 r A) :
    A.card ≤ diffExtremal r N := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hDiff⟩)

theorem sumExtremal_le (r N : ℕ) : sumExtremal r N ≤ N := by
  obtain ⟨A, hA, _, hc⟩ := exists_sumExtremal_set r N
  rw [← hc]
  simpa using Finset.card_le_card hA

theorem diffExtremal_le (r N : ℕ) : diffExtremal r N ≤ N := by
  obtain ⟨A, hA, _, hc⟩ := exists_diffExtremal_set r N
  rw [← hc]
  simpa using Finset.card_le_card hA

end JSP715
