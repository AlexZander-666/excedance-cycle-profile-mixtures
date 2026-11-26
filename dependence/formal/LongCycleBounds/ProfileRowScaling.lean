import LongCycleBounds.MixedProfilesVerified

namespace LongCycleBounds.CycleProfile
open Polynomial LongCycles

private theorem scale_product (m : Multiset ℕ) (z : ℝ) (w : ℕ → ℝ) :
    (m.map fun j => z ^ j * w j).prod = z ^ m.sum * (m.map w).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [ih, pow_add]; ring

/-- Multiplying every length-j weight by z^j scales the entire original n-letter row by z^n. -/
theorem row_rescale (n : ℕ) (z : ℝ) (w : ℕ → ℝ) :
    row n (fun j => z ^ j * w j) = C (z ^ n) * row n w := by
  classical
  unfold row
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases ok : Allowed 2 σ
  · have hs : σ.cycleType.sum = n := by
      rw [Equiv.Perm.sum_cycleType, support_univ_of_allowed ok (by decide)]
      simp
    simp only [if_pos ok, term, cycleWeight, scale_product, hs, map_mul, mul_assoc]
  · simp [ok]

theorem simple_unscale {n : ℕ} {p : ℝ[X]} {c : ℝ} (hc : c ≠ 0)
    (h : SimpleEndpointRow n (C c * p)) : SimpleEndpointRow n p := by
  unfold SimpleEndpointRow at *
  rw [roots_C_mul _ hc, splits_mul_iff_right (C_ne_zero.mpr hc) (Splits.C _)] at h
  exact h
end LongCycleBounds.CycleProfile
