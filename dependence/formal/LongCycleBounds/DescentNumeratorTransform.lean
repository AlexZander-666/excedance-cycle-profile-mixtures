import LongCycleBounds.DescentNecklaceCount
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! Exact extraction of the ordinary descent numerator from the positive necklace counts. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open PowerSeries Finset DescentTwoLetters

def numerator (n : ℕ) (d : ℕ → ℤ) : PowerSeries ℤ :=
  ∑ i ∈ range n, C (d i) * X ^ i

theorem coeff_numerator (n r : ℕ) (d : ℕ → ℤ) (hr : r < n) :
    coeff r (numerator n d) = d r := by
  simp only [numerator,map_sum,coeff_C_mul_X_pow]
  simp [hr]

theorem series_of_letters {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) :
    mk (fun r ↦ letters n (r+1) d) =
      numerator n d * (mk (fun j ↦ ((n+j).choose n : ℤ)) : PowerSeries ℤ) := by
  ext r
  rw [coeff_mk,numerator,Finset.sum_mul,map_sum]
  unfold letters
  apply sum_congr rfl
  intro i _
  rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul']
  by_cases hi : i ≤ r
  · rw [if_pos hi,coeff_mk]
    congr 3
    omega
  · rw [if_neg hi,Nat.choose_eq_zero_of_lt (show (r+1+n-1-i) < n by omega)]
    simp

theorem numerator_from_letters {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) :
    numerator n d = (1-X : PowerSeries ℤ)^(n+1) * PowerSeries.mk (fun r ↦ letters n (r+1) d) := by
  rw [series_of_letters hn, mul_comm, mul_assoc, mk_add_choose_mul_one_sub_pow_eq_one, mul_one]

theorem coeff_one_sub_X_pow (n j : ℕ) :
    coeff j ((1-X : PowerSeries ℤ)^n) = (-1:ℤ)^j * n.choose j := by
  have h := coeff_rescale ((X+1 : PowerSeries ℤ)^n) (-1) j
  have plus : coeff j ((X+1 : PowerSeries ℤ)^n) = (n.choose j : ℤ) := by
    simpa only [← Polynomial.coe_X, ← Polynomial.coe_one, ← Polynomial.coe_add,
      ← Polynomial.coe_pow,Polynomial.coeff_coe] using Polynomial.coeff_X_add_one_pow (R := ℤ) n j
  rw [plus] at h
  simpa [map_pow,map_add,sub_eq_add_neg,add_comm] using h

theorem invert_letters {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) {r : ℕ} (hr : r < n) :
    d r = ∑ j ∈ range (r+1), (-1:ℤ)^j * (n+1).choose j * letters n (r-j+1) d := by
  rw [← coeff_numerator n r d hr,numerator_from_letters hn,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_one_sub_X_pow,coeff_mk]

theorem coeff_row_from_necklaces {n r : ℕ} (hn : 0 < n) (hr : r < n) (k : ℕ) :
    (row n k).coeff r = ∑ j ∈ range (r+1), (-1:ℤ)^j * (n+1).choose j *
      (Nat.card (NecklaceContent n (r-j+1) k) : ℤ) := by
  simpa only [letters_eq_necklace_content hn] using invert_letters hn (row n k).coeff hr

/-- Division and binomial coefficients here are the natural/integer ones of the finite checker. -/
theorem coeff_row_positive_choose {n r : ℕ} (hn : 0 < n) (hr : r < n) (k : ℕ) :
    (row n k).coeff r = ∑ j ∈ range (r+1), (-1:ℤ)^j * (n+1).choose j *
      (∑ p : PositiveLengthProfile n k, ∏ i : Fin n,
        (Nat.choose (primitiveCount (i.val+1) (r-j+1) + (p.val i).val - 1) (p.val i).val : ℤ)) := by
  simpa only [letters_eq_positive_choose hn] using invert_letters hn (row n k).coeff hr

#print axioms coeff_row_positive_choose
#print axioms coeff_row_from_necklaces
end LongCycleBounds.DescentNecklace
