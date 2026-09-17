import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

/-! Conversion lemmas for the CRT02 unordered-sum convention.

The source counts positive integer sums and uses one sorted representative
of each unordered pair. Its sets in `[1,N]` do not contain zero. These lemmas
justify using natural-number sums in the construction interface.
-/

namespace JSP715.CRTConvention

def natSumReps (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun z => z.1 ≤ z.2 ∧ z.1 + z.2 = n

def integerSumReps (A : Finset ℕ) (s : ℤ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun z => z.1 ≤ z.2 ∧ (z.1 : ℤ) + z.2 = s

@[simp] theorem mem_natSumReps {A : Finset ℕ} {a b n : ℕ} :
    (a, b) ∈ natSumReps A n ↔ a ∈ A ∧ b ∈ A ∧ a ≤ b ∧ a + b = n := by
  simp [natSumReps, and_assoc]

@[simp] theorem mem_integerSumReps {A : Finset ℕ} {a b : ℕ} {s : ℤ} :
    (a, b) ∈ integerSumReps A s ↔
      a ∈ A ∧ b ∈ A ∧ a ≤ b ∧ (a : ℤ) + b = s := by
  simp [integerSumReps, and_assoc]

/-- Coercing the represented sum to integers preserves the entire fiber. -/
@[simp] theorem integerSumReps_natCast (A : Finset ℕ) (n : ℕ) :
    integerSumReps A (n : ℤ) = natSumReps A n := by
  ext ⟨a, b⟩
  simp only [mem_integerSumReps, mem_natSumReps]
  simp only [← Int.natCast_add, Int.natCast_inj]

@[simp] theorem integerSumReps_of_neg (A : Finset ℕ) {s : ℤ} (hs : s < 0) :
    integerSumReps A s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨a, b⟩ h
  have he := (mem_integerSumReps.mp h).2.2.2
  omega

/-- The sum-zero fiber consists precisely of the single possible diagonal. -/
theorem natSumReps_zero (A : Finset ℕ) :
    natSumReps A 0 = if 0 ∈ A then {(0, 0)} else ∅ := by
  ext ⟨a, b⟩
  by_cases h0 : 0 ∈ A
  · simp only [h0, ↓reduceIte, Finset.mem_singleton, Prod.mk.injEq, mem_natSumReps]
    constructor
    · intro h
      omega
    · rintro ⟨rfl, rfl⟩
      exact ⟨h0, h0, le_rfl, rfl⟩
  · simp only [h0, ↓reduceIte, Finset.notMem_empty, iff_false, mem_natSumReps]
    intro h
    have ha : a = 0 := by omega
    exact h0 (ha ▸ h.1)

@[simp] theorem natSumReps_zero_of_zero_not_mem {A : Finset ℕ} (hA : 0 ∉ A) :
    natSumReps A 0 = ∅ := by simp [natSumReps_zero, hA]

/-- A diagonal contributes once, without imposing strict inequality. -/
@[simp] theorem diagonal_mem_natSumReps {A : Finset ℕ} {a : ℕ} :
    (a, a) ∈ natSumReps A (a + a) ↔ a ∈ A := by simp

/-- For a distinct pair, its reverse is excluded by the sorted convention. -/
theorem reverse_not_mem_natSumReps (A : Finset ℕ) {a b n : ℕ} (hab : a < b) :
    (b, a) ∉ natSumReps A n := by
  intro h
  exact Nat.not_le_of_lt hab (mem_natSumReps.mp h).2.2.1

/-- Bounds on all integer fibers and all natural fibers are equivalent. -/
theorem all_nat_iff_all_integer (r : ℕ) (A : Finset ℕ) :
    (∀ n : ℕ, (natSumReps A n).card ≤ r) ↔
      ∀ s : ℤ, (integerSumReps A s).card ≤ r := by
  constructor
  · intro h s
    by_cases hs : s < 0
    · simp [integerSumReps_of_neg A hs]
    · have he : (s.toNat : ℤ) = s := Int.toNat_of_nonneg (by omega)
      rw [← he, integerSumReps_natCast]
      exact h _
  · intro h n
    simpa using h (n : ℤ)

/-- Exact CRT02 convention equivalence for sets without zero, including `[1,N]`. -/
theorem all_nat_iff_positive_integer (r : ℕ) {A : Finset ℕ} (hA : 0 ∉ A) :
    (∀ n : ℕ, (natSumReps A n).card ≤ r) ↔
      ∀ s : ℤ, 0 < s → (integerSumReps A s).card ≤ r := by
  constructor
  · intro h s _
    exact (all_nat_iff_all_integer r A).mp h s
  · intro h n
    by_cases hn : n = 0
    · simp [hn, hA]
    · have hp : (0 : ℤ) < n := by omega
      simpa using h (n : ℤ) hp

theorem all_nat_iff_positive_nat (r : ℕ) {A : Finset ℕ} (hA : 0 ∉ A) :
    (∀ n : ℕ, (natSumReps A n).card ≤ r) ↔
      ∀ n : ℕ, 0 < n → (natSumReps A n).card ≤ r := by
  constructor
  · exact fun h n _ => h n
  · intro h n
    by_cases hn : n = 0
    · simp [hn, hA]
    · exact h n (by omega)

theorem interval_convention (r N : ℕ) {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) :
    (∀ n : ℕ, (natSumReps A n).card ≤ r) ↔
      ∀ s : ℤ, 0 < s → (integerSumReps A s).card ≤ r := by
  apply all_nat_iff_positive_integer
  intro h0
  have := (Finset.mem_Icc.mp (hA h0)).1
  omega

end JSP715.CRTConvention

#print axioms JSP715.CRTConvention.interval_convention
