import Mathlib.RingTheory.ZMod.Torsion
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
A kernel-checked Ruzsa modular Sidon base for the amplification in CRT02 Lemma 2.2.
The paper uses a Singer base with parameters `(p²+p+1,p+1)`. This independent
implementation uses `(p*(p-1),p-1)` and therefore has a different exact finite
parameterization, but the same limiting normalized base cardinality.
-/

namespace JSP715.CRT

noncomputable section

/-- Unordered uniqueness of sums after reduction modulo `m`. -/
def ModularSidon (m : ℕ) (C : Finset ℕ) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ d ∈ C,
    (a + b) % m = (c + d) % m →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A monic quadratic is determined by its sum and product of roots. -/
private lemma sum_product_pair {K : Type*} [Field K] {a b c d : K}
    (hs : a + b = c + d) (hp : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hfactor : (a - c) * (a - d) = 0 := by
    calc
      (a - c) * (a - d) = a * (a + b - (c + d)) + (c * d - a * b) := by ring
      _ = 0 := by rw [hs, hp]; ring
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    have hac := sub_eq_zero.mp h
    exact ⟨hac, by rw [hac] at hs; exact add_left_cancel hs⟩
  · right
    have had := sub_eq_zero.mp h
    refine ⟨had, ?_⟩
    rw [had, add_comm c d] at hs
    exact add_left_cancel hs

/-- Ruzsa construction, initially with modulus `(p-1)*p`. -/
private theorem exists_base_mul (p : ℕ) (hp : p.Prime) :
    ∃ C : Finset ℕ, C ⊆ Finset.range ((p - 1) * p) ∧
      C.card = p - 1 ∧ ModularSidon ((p - 1) * p) C := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hpm : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  let m := (p - 1) * p
  have hm : 0 < m := Nat.mul_pos hpm hp.pos
  let : NeZero m := ⟨hm.ne'⟩
  obtain ⟨g, hg⟩ := (HasEnoughRootsOfUnity.prim :
    ∃ g : ZMod p, IsPrimitiveRoot g (p - 1))
  have hcop : (p - 1).Coprime p := by
    simp [Nat.coprime_iff_gcd_eq_one, hp.one_le]
  let e : ZMod m ≃+* ZMod (p - 1) × ZMod p := ZMod.chineseRemainder hcop
  let point : Fin (p - 1) → ZMod (p - 1) × ZMod p :=
    fun i => ((i.val : ZMod (p - 1)), g ^ i.val)
  let encode : Fin (p - 1) → ℕ := fun i => (e.symm (point i)).val
  have hdecode (i : Fin (p - 1)) : e (encode i : ZMod m) = point i := by
    simp [encode]
  have hinj : Function.Injective encode := by
    intro i j h
    have he : point i = point j := by rw [← hdecode i, ← hdecode j, h]
    have hgpow : g ^ i.val = g ^ j.val := congrArg Prod.snd he
    exact Fin.ext (hg.pow_inj i.isLt j.isLt hgpow)
  let C := Finset.univ.image encode
  refine ⟨C, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (ZMod.val_lt _)
  · rw [Finset.card_image_of_injective _ hinj]
    exact Fintype.card_fin (p - 1)
  · intro a ha b hb c hc d hd hmod
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hd
    have hz : ((encode i + encode j : ℕ) : ZMod m) =
        ((encode k + encode l : ℕ) : ZMod m) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod
    have hpoints : point i + point j = point k + point l := by
      have he := congrArg e hz
      simpa only [Nat.cast_add, map_add, hdecode] using he
    have hexponent : ((i.val + j.val : ℕ) : ZMod (p - 1)) =
        ((k.val + l.val : ℕ) : ZMod (p - 1)) := by
      simpa only [point, Prod.fst_add, Nat.cast_add] using congrArg Prod.fst hpoints
    have hexpmod : (i.val + j.val) ≡ (k.val + l.val) [MOD (p - 1)] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hexponent
    have hproduct : (g ^ i.val) * (g ^ j.val) = (g ^ k.val) * (g ^ l.val) := by
      simpa only [pow_add] using pow_eq_pow_of_modEq hexpmod hg.pow_eq_one
    have hsum : g ^ i.val + g ^ j.val = g ^ k.val + g ^ l.val :=
      congrArg Prod.snd hpoints
    rcases sum_product_pair hsum hproduct with h | h
    · left
      have hik : i = k := Fin.ext (hg.pow_inj i.isLt k.isLt h.1)
      have hjl : j = l := Fin.ext (hg.pow_inj j.isLt l.isLt h.2)
      exact ⟨congrArg encode hik, congrArg encode hjl⟩
    · right
      have hil : i = l := Fin.ext (hg.pow_inj i.isLt l.isLt h.1)
      have hjk : j = k := Fin.ext (hg.pow_inj j.isLt k.isLt h.2)
      exact ⟨congrArg encode hil, congrArg encode hjk⟩

/-- Every prime supplies a modular Sidon base of cardinality `p-1`. -/
theorem exists_base (p : ℕ) (hp : p.Prime) :
    ∃ C : Finset ℕ, C ⊆ Finset.range (p * (p - 1)) ∧
      C.card = p - 1 ∧ ModularSidon (p * (p - 1)) C := by
  simpa only [Nat.mul_comm (p - 1) p] using exists_base_mul p hp

end

end JSP715.CRT

#print axioms JSP715.CRT.exists_base
