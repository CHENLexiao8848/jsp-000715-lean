import JSP715.CRTBase
import JSP715.CRTPattern

namespace JSP715.CRT

/-- The CRT02 convention: one representative of each unordered pair, including diagonals. -/
def sumReps (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun z => z.1 ≤ z.2 ∧ z.1 + z.2 = n

def IsSumB2 (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n, (sumReps A n).card ≤ r

/-- CRT02 Lemma 2.2, before translating the representatives by one. -/
def paste (m : ℕ) (C I : Finset ℕ) : Finset ℕ :=
  (C ×ˢ I).image fun z => z.1 + m * z.2

lemma paste_decode {m : ℕ} (hm : 0 < m) {C I : Finset ℕ}
    (hC : C ⊆ Finset.range m) {x : ℕ} (hx : x ∈ paste m C I) :
    x % m ∈ C ∧ x / m ∈ I := by
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hc, hi⟩ := Finset.mem_product.mp hci
  have hcm := Finset.mem_range.mp (hC hc)
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hcm, Nat.add_mul_div_left,
    Nat.div_eq_of_lt hcm, hm] using And.intro hc hi

lemma paste_card {m : ℕ} (_hm : 0 < m) {C I : Finset ℕ}
    (hC : C ⊆ Finset.range m) : (paste m C I).card = C.card * I.card := by
  rw [paste, Finset.card_image_of_injOn, Finset.card_product]
  intro x hx y hy heq
  have hxl := Finset.mem_range.mp (hC (Finset.mem_product.mp hx).1)
  have hyl := Finset.mem_range.mp (hC (Finset.mem_product.mp hy).1)
  have hc : x.1 = y.1 := by
    have h := congrArg (· % m) heq
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] using h
  have hi : x.2 = y.2 := by nlinarith
  exact Prod.ext hc hi

lemma paste_bound {m D : ℕ} {C I : Finset ℕ}
    (hC : C ⊆ Finset.range m) (hI : ∀ i ∈ I, i < D)
    {x : ℕ} (hx : x ∈ paste m C I) : x < m * D := by
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hc, hi⟩ := Finset.mem_product.mp hci
  have hcm := Finset.mem_range.mp (hC hc)
  have hiD := hI i hi
  have := Nat.mul_le_mul_left m (show i + 1 ≤ D by omega)
  nlinarith

/-- Orient a numerical representation by residue; the diagonal is unchanged. -/
def residueOrder (m : ℕ) (z : ℕ × ℕ) : ℕ × ℕ :=
  if z.1 % m ≤ z.2 % m then z else z.swap

lemma residueOrder_sum (m : ℕ) (z : ℕ × ℕ) :
    (residueOrder m z).1 + (residueOrder m z).2 = z.1 + z.2 := by
  unfold residueOrder
  split_ifs <;> simp [Nat.add_comm]

lemma residueOrder_le (m : ℕ) (z : ℕ × ℕ) :
    (residueOrder m z).1 % m ≤ (residueOrder m z).2 % m := by
  unfold residueOrder
  split_ifs with h <;> simp_all <;> omega

lemma residueOrder_mem {m : ℕ} {A : Finset ℕ} {z : ℕ × ℕ}
    (h : z.1 ∈ A ∧ z.2 ∈ A) :
    (residueOrder m z).1 ∈ A ∧ (residueOrder m z).2 ∈ A := by
  unfold residueOrder
  split_ifs <;> simp_all

lemma residueOrder_inj {m : ℕ} {z w : ℕ × ℕ}
    (hz : z.1 ≤ z.2) (hw : w.1 ≤ w.2)
    (h : residueOrder m z = residueOrder m w) : z = w := by
  unfold residueOrder at h
  split_ifs at h <;> have h1 := congrArg Prod.fst h <;>
    have h2 := congrArg Prod.snd h
  all_goals try simp only [Prod.fst_swap, Prod.snd_swap] at h1 h2
  all_goals apply Prod.ext <;> omega





/-- Ordered-residue representatives of equal sums have identical residues. -/
lemma oriented_residues {m : ℕ} (hm : 0 < m) {C I : Finset ℕ}
    (hC : C ⊆ Finset.range m) (hs : ModularSidon m C)
    {z w : ℕ × ℕ} (hz : z.1 ∈ paste m C I ∧ z.2 ∈ paste m C I)
    (hw : w.1 ∈ paste m C I ∧ w.2 ∈ paste m C I)
    (he : z.1 + z.2 = w.1 + w.2) :
    (residueOrder m z).1 % m = (residueOrder m w).1 % m ∧
    (residueOrder m z).2 % m = (residueOrder m w).2 % m := by
  have hz' := residueOrder_mem (m := m) hz
  have hw' := residueOrder_mem (m := m) hw
  have ha := (paste_decode hm hC hz'.1).1
  have hb := (paste_decode hm hC hz'.2).1
  have hc := (paste_decode hm hC hw'.1).1
  have hd := (paste_decode hm hC hw'.2).1
  have hsum : (residueOrder m z).1 + (residueOrder m z).2 =
      (residueOrder m w).1 + (residueOrder m w).2 := by
    rw [residueOrder_sum, residueOrder_sum, he]
  have hmod := congrArg (· % m) hsum
  have hcollision := hs _ ha _ hb _ hc _ hd (by simpa [Nat.add_mod] using hmod)
  have hzle := residueOrder_le m z
  have hwle := residueOrder_le m w
  rcases hcollision with h | h
  · exact h
  · omega

lemma ordered_quotient_sum {m : ℕ} (hm : 0 < m) {z w : ℕ × ℕ}
    (hs : z.1 + z.2 = w.1 + w.2)
    (h1 : z.1 % m = w.1 % m) (h2 : z.2 % m = w.2 % m) :
    z.1 / m + z.2 / m = w.1 / m + w.2 / m := by
  have hza := Nat.mod_add_div z.1 m
  have hzb := Nat.mod_add_div z.2 m
  have hwa := Nat.mod_add_div w.1 m
  have hwb := Nat.mod_add_div w.2 m
  have hmuls : m * (z.1 / m + z.2 / m) = m * (w.1 / m + w.2 / m) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  exact Nat.eq_of_mul_eq_mul_left hm hmuls

/-- The parametric CRT02 pasting bound. A residue tie includes the diagonal once. -/
theorem paste_isSumB2 {m r : ℕ} (hm : 0 < m) {C I : Finset ℕ}
    (hC : C ⊆ Finset.range m) (hs : ModularSidon m C)
    (hI : ∀ n, ((I ×ˢ I).filter fun z => z.1 + z.2 = n).card ≤ r) :
    IsSumB2 r (paste m C I) := by
  intro n
  classical
  by_cases hempty : sumReps (paste m C I) n = ∅
  · simp [hempty]
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hw' : (w.1 ∈ paste m C I ∧ w.2 ∈ paste m C I) ∧
      w.1 ≤ w.2 ∧ w.1 + w.2 = n := by simpa [sumReps] using hw
  let f : ℕ × ℕ → ℕ × ℕ := fun z =>
    ((residueOrder m z).1 / m, (residueOrder m z).2 / m)
  let t := (f w).1 + (f w).2
  apply le_trans (Finset.card_le_card_of_injOn f (t :=
    (I ×ˢ I).filter fun z => z.1 + z.2 = t) ?_ ?_) (hI t)
  · intro z hz
    have hz' : (z.1 ∈ paste m C I ∧ z.2 ∈ paste m C I) ∧
        z.1 ≤ z.2 ∧ z.1 + z.2 = n := by simpa [sumReps] using hz
    have hzmem := residueOrder_mem (m := m) hz'.1
    have hres := oriented_residues hm hC hs hz'.1 hw'.1 (by omega)
    have he : (residueOrder m z).1 + (residueOrder m z).2 =
        (residueOrder m w).1 + (residueOrder m w).2 := by
      rw [residueOrder_sum, residueOrder_sum]; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(paste_decode hm hC hzmem.1).2, (paste_decode hm hC hzmem.2).2⟩,
      ordered_quotient_sum hm he hres.1 hres.2⟩
  · intro z hz v hv hcode
    have hz' : (z.1 ∈ paste m C I ∧ z.2 ∈ paste m C I) ∧
        z.1 ≤ z.2 ∧ z.1 + z.2 = n := by simpa [sumReps] using hz
    have hv' : (v.1 ∈ paste m C I ∧ v.2 ∈ paste m C I) ∧
        v.1 ≤ v.2 ∧ v.1 + v.2 = n := by simpa [sumReps] using hv
    have hres := oriented_residues hm hC hs hz'.1 hv'.1 (by omega)
    have hq1 := congrArg Prod.fst hcode
    have hq2 := congrArg Prod.snd hcode
    change (residueOrder m z).1 / m = (residueOrder m v).1 / m at hq1
    change (residueOrder m z).2 / m = (residueOrder m v).2 / m at hq2
    have h1 := Nat.mod_add_div (residueOrder m z).1 m
    have h2 := Nat.mod_add_div (residueOrder m z).2 m
    have h3 := Nat.mod_add_div (residueOrder m v).1 m
    have h4 := Nat.mod_add_div (residueOrder m v).2 m
    have hr1 := hres.1
    have hr2 := hres.2
    rw [hr1, hq1] at h1
    rw [hr2, hq2] at h2
    apply residueOrder_inj (m := m) hz'.2.1 hv'.2.1
    apply Prod.ext <;> omega

/-- Translate the final set so that its ambient interval starts at one. -/
lemma isSumB2_succ {r : ℕ} {A : Finset ℕ} (hA : IsSumB2 r A) :
    IsSumB2 r (A.image Nat.succ) := by
  intro n
  apply le_trans (Finset.card_le_card_of_injOn
    (fun z : ℕ × ℕ => (z.1 - 1, z.2 - 1)) (t := sumReps A (n - 2)) ?_ ?_)
    (hA (n - 2))
  · intro z hz
    obtain ⟨hzmem, hle, hsum⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hzmem
    obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp hz1
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp hz2
    have hza : z.1 - 1 = a := by omega
    have hzb : z.2 - 1 = b := by omega
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨by simpa only [hza] using ha,
      by simpa only [hzb] using hb⟩,
      by dsimp; omega, by dsimp; omega⟩
  · intro z hz w hw he
    have hzmem := (Finset.mem_filter.mp hz).1
    have hwmem := (Finset.mem_filter.mp hw).1
    obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp (Finset.mem_product.mp hzmem).1
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp (Finset.mem_product.mp hzmem).2
    obtain ⟨c, hc, hceq⟩ := Finset.mem_image.mp (Finset.mem_product.mp hwmem).1
    obtain ⟨d, hd, hdeq⟩ := Finset.mem_image.mp (Finset.mem_product.mp hwmem).2
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext <;> dsimp at h1 h2 ⊢ <;> omega

/-- CRT02's exact sparse pattern and generic pasting, shifted into the positive integers. -/
def construction (m : ℕ) (C : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (paste m C (layer r)).image Nat.succ

theorem construction_card {m r : ℕ} (hm : 0 < m) (hr : 1 ≤ r) {C : Finset ℕ}
    (hC : C ⊆ Finset.range m) :
    (construction m C r).card = C.card * (r + r / 2) := by
  rw [construction, Finset.card_image_of_injective _ Nat.succ_injective,
    paste_card hm hC, layer_card hr]

theorem construction_subset {m r : ℕ} (hr : 1 ≤ r) {C : Finset ℕ}
    (hC : C ⊆ Finset.range m) :
    construction m C r ⊆ Finset.Icc 1 (m * (r + 2 * (r / 2))) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hbound := paste_bound hC (layer_bound hr) hy
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem construction_isSumB2 {m r : ℕ} (hm : 0 < m) (hr : 1 ≤ r) {C : Finset ℕ}
    (hC : C ⊆ Finset.range m) (hs : ModularSidon m C) :
    IsSumB2 r (construction m C r) :=
  isSumB2_succ (paste_isSumB2 hm hC hs (layer_ordered hr))

/-- Every prime yields a genuine finite B₂[r] set, with the exact CRT02 layer factor. -/
theorem finite_construction {r p : ℕ} (hr : 1 ≤ r) (hp : p.Prime) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (p * (p - 1) * (r + 2 * (r / 2))) ∧
      IsSumB2 r A ∧ A.card = (p - 1) * (r + r / 2) := by
  obtain ⟨C, hC, hcard, hsidon⟩ := exists_base p hp
  have hm : 0 < p * (p - 1) := Nat.mul_pos hp.pos (Nat.sub_pos_of_lt hp.one_lt)
  exact ⟨construction (p * (p - 1)) C r, construction_subset hr hC,
    construction_isSumB2 hm hr hC hsidon, by rw [construction_card hm hr hC, hcard]⟩

end JSP715.CRT

