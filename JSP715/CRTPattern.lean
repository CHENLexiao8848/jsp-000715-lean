import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace JSP715.CRT

/-- The sparse layer pattern of CRT02, Lemma 2.3. -/
def layer (r : ℕ) : Finset ℕ :=
  Finset.range r ∪ (Finset.Icc 1 (r / 2)).image (fun j => r - 1 + 2 * j)

/-- Ordered representations; a diagonal pair occurs once. -/
def orderedReps (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun x => x.1 + x.2 = n)

theorem mem_layer {r a : ℕ} :
    a ∈ layer r ↔ a < r ∨ ∃ j, 1 ≤ j ∧ j ≤ r / 2 ∧ a = r - 1 + 2 * j := by
  simp only [layer, Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_Icc]
  aesop

theorem mem_orderedReps {A : Finset ℕ} {n : ℕ} {x : ℕ × ℕ} :
    x ∈ orderedReps A n ↔ x.1 ∈ A ∧ x.2 ∈ A ∧ x.1 + x.2 = n := by
  simp [orderedReps, and_assoc]

theorem layer_card {r : ℕ} (hr : 1 ≤ r) : (layer r).card = r + r / 2 := by
  have hd : Disjoint (Finset.range r)
      ((Finset.Icc 1 (r / 2)).image (fun j => r - 1 + 2 * j)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_Icc] at hj
    omega
  rw [layer, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (by intro a b h; dsimp at h; omega)]
  simp

theorem layer_bound {r : ℕ} (hr : 1 ≤ r) (a : ℕ) (ha : a ∈ layer r) :
    a < r + 2 * (r / 2) := by
  rcases mem_layer.mp ha with h | ⟨j, hj, hj', rfl⟩ <;> omega

/-- Every point in the upper part of the pattern has a missing predecessor. -/
theorem layer_high_gap {r a b : ℕ} (hr : 1 ≤ r)
    (ha : a ∈ layer r) (hb : b ∈ layer r) (hra : r ≤ a) : b + 1 ≠ a := by
  rcases mem_layer.mp ha with ha | ⟨j, hj, hj', ha⟩
  · omega
  rcases mem_layer.mp hb with hb | ⟨k, hk, hk', hb⟩ <;> omega

private theorem small_sum_ordered {r n : ℕ} (hr : 1 ≤ r) (hn : n < 2 * r) :
    (orderedReps (layer r) n).card ≤ r := by
  let f : ℕ × ℕ → ℕ := fun x => if x.1 < r then x.1 else n - x.1 + 1
  have hf : Set.MapsTo f (orderedReps (layer r) n) (Finset.range r) := by
    intro x hx
    obtain ⟨ha, hb, hs⟩ := mem_orderedReps.mp hx
    rw [Finset.mem_coe, Finset.mem_range]
    dsimp [f]
    split_ifs with h
    · exact h
    · rcases mem_layer.mp ha with ha | ⟨j, hj, hj', ha⟩ <;> omega
  have hi : Set.InjOn f (orderedReps (layer r) n) := by
    intro x hx y hy he
    obtain ⟨ha, hb, hs⟩ := mem_orderedReps.mp hx
    obtain ⟨hc, hd, ht⟩ := mem_orderedReps.mp hy
    dsimp [f] at he
    split_ifs at he with h h' h'
    · apply Prod.ext <;> omega
    · have hg := layer_high_gap hr hc hb (by omega)
      omega
    · have hg := layer_high_gap hr ha hd (by omega)
      omega
    · apply Prod.ext <;> omega
  simpa using Finset.card_le_card_of_injOn f hf hi

private theorem large_sum_ordered {r n : ℕ} (hr : 1 ≤ r) (hn : 2 * r ≤ n) :
    (orderedReps (layer r) n).card ≤ r := by
  let f : ℕ × ℕ → ℕ := fun x =>
    if x.1 < r then r / 2 + x.1 / 2 else (x.1 - (r - 1)) / 2 - 1
  have hf : Set.MapsTo f (orderedReps (layer r) n) (Finset.range r) := by
    intro x hx
    obtain ⟨ha, hb, hs⟩ := mem_orderedReps.mp hx
    rw [Finset.mem_coe, Finset.mem_range]
    dsimp [f]
    split_ifs with h
    · omega
    · rcases mem_layer.mp ha with ha | ⟨j, hj, hj', ha⟩ <;> omega
  have hi : Set.InjOn f (orderedReps (layer r) n) := by
    intro x hx y hy he
    obtain ⟨ha, hb, hs⟩ := mem_orderedReps.mp hx
    obtain ⟨hc, hd, ht⟩ := mem_orderedReps.mp hy
    dsimp [f] at he
    split_ifs at he with h h' h'
    · have hb' : r ≤ x.2 := by omega
      have hd' : r ≤ y.2 := by omega
      rcases mem_layer.mp hb with hb | ⟨j, hj, hj', hb⟩
      · omega
      rcases mem_layer.mp hd with hd | ⟨k, hk, hk', hd⟩
      · omega
      apply Prod.ext <;> omega
    · rcases mem_layer.mp hc with hc | ⟨j, hj, hj', hc⟩ <;> omega
    · rcases mem_layer.mp ha with ha | ⟨j, hj, hj', ha⟩ <;> omega
    · rcases mem_layer.mp ha with ha | ⟨j, hj, hj', ha⟩
      · omega
      rcases mem_layer.mp hc with hc | ⟨k, hk, hk', hc⟩
      · omega
      apply Prod.ext <;> omega
  simpa using Finset.card_le_card_of_injOn f hf hi

/-- CRT02 Lemma 2.3: each integer has at most `r` ordered layer representations. -/
theorem layer_ordered {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (orderedReps (layer r) n).card ≤ r := by
  rcases lt_or_ge n (2 * r) with hn | hn
  · exact small_sum_ordered hr hn
  · exact large_sum_ordered hr hn

end JSP715.CRT
