import JSP715.DifferenceUpper
import Mathlib.Order.Interval.Finset.Nat

/-! Exact transport of bounded positive differences from natural to integer sets. -/

namespace JSP715.DifferenceBridge

def intImage (A : Finset ℕ) : Finset ℤ := A.image (fun n : ℕ => (n : ℤ))

def natDiffReps (A : Finset ℕ) (d : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p => p.1 - p.2 = d

def IsNatDiffB2 (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → (natDiffReps A d).card ≤ r

@[simp] theorem mem_natDiffReps {A : Finset ℕ} {a b d : ℕ} :
    (a, b) ∈ natDiffReps A d ↔ a ∈ A ∧ b ∈ A ∧ a - b = d := by
  simp [natDiffReps, and_assoc]

@[simp] theorem card_intImage (A : Finset ℕ) : (intImage A).card = A.card := by
  apply Finset.card_image_of_injective
  intro a b h
  exact Int.natCast_inj.mp h

theorem subset_intImage {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Finset.Icc 1 N) :
    intImage A ⊆ Finset.Icc 1 (N : ℤ) := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp (hA ha)
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast ha1, by exact_mod_cast haN⟩

/-- Coercing a pair gives the entire integer fiber for each positive difference. -/
theorem diffReps_intImage_eq_image (A : Finset ℕ) {d : ℕ} (hd : 0 < d) :
    Difference.diffReps (intImage A) (d : ℤ) =
      (natDiffReps A d).image (fun p : ℕ × ℕ => ((p.1 : ℤ), (p.2 : ℤ))) := by
  ext ⟨a, b⟩
  constructor
  · intro h
    obtain ⟨ha, hb, hab⟩ := Difference.mem_diffReps.mp h
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨(a', b'),
      mem_natDiffReps.mpr ⟨ha', hb', by omega⟩, rfl⟩
  · intro h
    obtain ⟨⟨a', b'⟩, hp, he⟩ := Finset.mem_image.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨ha', hb', hab⟩ := mem_natDiffReps.mp hp
    exact Difference.mem_diffReps.mpr
      ⟨Finset.mem_image.mpr ⟨a', ha', rfl⟩,
        Finset.mem_image.mpr ⟨b', hb', rfl⟩, by omega⟩

/-- The positive fibers have exactly equal cardinality, not merely a one-way bound. -/
theorem card_diffReps_intImage (A : Finset ℕ) {d : ℕ} (hd : 0 < d) :
    (Difference.diffReps (intImage A) (d : ℤ)).card = (natDiffReps A d).card := by
  rw [diffReps_intImage_eq_image A hd]
  apply Finset.card_image_of_injective
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simpa only [Prod.mk.injEq, Int.natCast_inj] using h

theorem isDiffB2_intImage_iff (r : ℕ) (A : Finset ℕ) :
    Difference.IsDiffB2 r (intImage A) ↔ IsNatDiffB2 r A := by
  constructor
  · intro h d hd
    have hb := h (d : ℤ) (by exact_mod_cast hd)
    rwa [card_diffReps_intImage A hd] at hb
  · intro h d hd
    have hn : 0 < d.toNat := by omega
    have he : (d.toNat : ℤ) = d := by omega
    rw [← he, card_diffReps_intImage A hn]
    exact h d.toNat hn

/-- The exact finite second-moment estimate transported to natural-number sets. -/
theorem nat_diff_card_sq_mul_le_sharp {r N L : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (h : IsNatDiffB2 r A) :
    A.card ^ 2 * L ^ 2 ≤ (N + L - 1) *
      (A.card * L + r * L * (L - 1)) := by
  simpa only [card_intImage] using Difference.diff_card_sq_mul_le_sharp
    (L := L) (subset_intImage hA) ((isDiffB2_intImage_iff r A).mpr h)

theorem nat_diff_card_sq_le {r N L : ℕ} {A : Finset ℕ} (hL : 0 < L)
    (hA : A ⊆ Finset.Icc 1 N) (h : IsNatDiffB2 r A) :
    (A.card : ℝ) ^ 2 ≤ ((N : ℝ) + L) * ((A.card : ℝ) / L + r) := by
  simpa only [card_intImage] using Difference.diff_card_sq_le hL
    (subset_intImage hA) ((isDiffB2_intImage_iff r A).mpr h)

/-- Uniform unconditional upper bound for all sufficiently large intervals. -/
theorem nat_diff_upper_eventually (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → IsNatDiffB2 r A →
      (A.card : ℝ) ≤ (Real.sqrt r + ε) * Real.sqrt N := by
  obtain ⟨N₀, hN₀⟩ := Difference.diff_card_upper_eventually r hε
  refine ⟨N₀, fun N hN A hA h => ?_⟩
  simpa only [card_intImage] using hN₀ N hN (intImage A)
    (subset_intImage hA) ((isDiffB2_intImage_iff r A).mpr h)

end JSP715.DifferenceBridge
