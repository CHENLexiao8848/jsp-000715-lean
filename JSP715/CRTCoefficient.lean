import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

namespace JSP715.CRT

open Filter
noncomputable section

/-- The exact density factor of the CRT02 digit set. -/
def coefficient (r : ℕ) : ℝ :=
  ((r + r / 2 : ℕ) : ℝ) / Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ)

private lemma normalize_sqrt_product {x y z s : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    y * s / Real.sqrt (x * y * z) =
      s / Real.sqrt z * Real.sqrt (y / x) := by
  rw [Real.sqrt_mul (mul_nonneg hx.le hy.le), Real.sqrt_mul hx.le,
    Real.sqrt_div hy.le]
  have hxs := (Real.sqrt_pos.mpr hx).ne'
  have hys := (Real.sqrt_pos.mpr hy).ne'
  have hzs := (Real.sqrt_pos.mpr hz).ne'
  field_simp
  rw [Real.sq_sqrt hy.le]
  ring

/-- Exact finite normalization for the Ruzsa base used with CRT02 pasting. -/
lemma ratio_identity {p D S : ℕ} (hp : 1 < p) (hD : 0 < D) :
    (((p - 1) * S : ℕ) : ℝ) /
        Real.sqrt ((p * (p - 1) * D : ℕ) : ℝ) =
      (S : ℝ) / Real.sqrt D * Real.sqrt (((p - 1 : ℕ) : ℝ) / (p : ℝ)) := by
  have hp' : (0 : ℝ) < p := by positivity
  have hq' : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have hD' : (0 : ℝ) < D := by positivity
  simpa only [Nat.cast_mul] using
    (normalize_sqrt_product (s := (S : ℝ)) hp' hq' hD')

/-- Increasing enumeration of the primes, starting at index zero. -/
def primes (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma primes_prime (n : ℕ) : (primes n).Prime := Nat.prime_nth_prime n

lemma primes_tendsto : Tendsto primes atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  have h := Nat.add_two_le_nth_prime n
  change b ≤ Nat.nth Nat.Prime n
  omega


/-- The relative loss of the Ruzsa modular base tends to zero. -/
lemma prime_ratio_tendsto :
    Tendsto (fun n => (((primes n - 1 : ℕ) : ℝ) / (primes n : ℝ)))
      atTop (nhds 1) := by
  have hc : Tendsto (fun n => (primes n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp primes_tendsto
  have hi : Tendsto (fun n => (primes n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hc
  have he : ∀ n, (((primes n - 1 : ℕ) : ℝ) / (primes n : ℝ)) =
      1 - (primes n : ℝ)⁻¹ := by
    intro n
    have hp := (primes_prime n).two_le
    have hp0 : (primes n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub (by omega : 1 ≤ primes n), Nat.cast_one,
      sub_div, div_self hp0, one_div]
  simp_rw [he]
  convert tendsto_const_nhds.sub hi using 1
  norm_num

/-- The finite CRT02 amplification attains its exact coefficient along prime moduli. -/
lemma ratio_tendsto {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun n =>
      ((((primes n - 1) * (r + r / 2) : ℕ) : ℝ) /
        Real.sqrt ((primes n * (primes n - 1) *
          (r + 2 * (r / 2)) : ℕ) : ℝ)))
      atTop (nhds (coefficient r)) := by
  have hs := (Real.continuous_sqrt.tendsto 1).comp prime_ratio_tendsto
  have hm := hs.const_mul (coefficient r)
  simp only [Real.sqrt_one, mul_one] at hm
  convert hm using 1
  funext n
  exact ratio_identity (primes_prime n).one_lt (by omega)


end
end JSP715.CRT
