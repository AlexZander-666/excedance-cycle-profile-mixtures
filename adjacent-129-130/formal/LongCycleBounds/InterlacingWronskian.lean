import LongCycles.Statement
import Mathlib

/-! A sign test for weak interlacing with common or repeated roots, at a point
where the two real polynomials have opposite signs. -/
noncomputable section
namespace LongCycleBounds.RootTests
open Polynomial Finset LongCycles

private theorem factors_at {d : ℕ} (r : Fin d → ℝ) (t : ℝ) :
    (linearFactors r).eval t = ∏ i, (t-r i) := by
  simp [linearFactors,eval_prod]

private theorem factors_deriv_at {d : ℕ} (r : Fin d → ℝ) (t : ℝ) :
    (linearFactors r).derivative.eval t = ∑ i, ∏ j ∈ univ.erase i, (t-r j) := by
  simp [linearFactors,derivative_prod_finset,eval_finsetSum,eval_prod]

private theorem factor_monic {d : ℕ} (r : Fin d → ℝ) : (linearFactors r).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_sub_C _)

private theorem paired_derivative {d : ℕ} (r s : Fin d → ℝ) (t : ℝ) :
    (linearFactors s).derivative.eval t * (linearFactors r).eval t -
      (linearFactors r).derivative.eval t * (linearFactors s).eval t =
    ∑ i, (s i-r i) * ∏ j ∈ univ.erase i, ((t-r j)*(t-s j)) := by
  simp only [factors_deriv_at,factors_at,sum_mul,←sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  have a := prod_erase_mul univ (fun j ↦ t-r j) hi
  have b := prod_erase_mul univ (fun j ↦ t-s j) hi
  rw [←a,←b,prod_mul_distrib]
  ring

private theorem obstruction_geometry {d : ℕ} {r : Fin d → ℝ} {s : Fin (d+1) → ℝ}
    (order : Monotone s) (alt : ∀ i, s i.castSucc ≤ r i ∧ r i ≤ s i.succ)
    (t : ℝ) (negative : (t-s (Fin.last d)) * ∏ i, ((t-r i)*(t-s i.castSucc)) < 0) :
    t < s (Fin.last d) ∧ ∀ i, 0 ≤ (t-r i)*(t-s i.castSucc) := by
  have below : t < s (Fin.last d) := by
    by_contra! bad
    apply (not_lt_of_ge (mul_nonneg (sub_nonneg.mpr bad) (prod_nonneg (fun i _ ↦ ?_)))) negative
    have h := (order (Fin.le_last i.succ)).trans bad
    exact mul_nonneg (sub_nonneg.mpr ((alt i).2.trans h))
      (sub_nonneg.mpr ((alt i).1.trans ((alt i).2.trans h)))
  refine ⟨below,fun i ↦ ?_⟩
  by_contra! opposite
  have left : s i.castSucc < t := by
    by_contra! ht
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (ht.trans (alt i).1)) (sub_nonpos.mpr ht))) opposite
  have right : t < r i := by
    by_contra! ht
    exact (not_lt_of_ge (mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr ((alt i).1.trans ht)))) opposite
  have others : 0 ≤ ∏ j ∈ univ.erase i, ((t-r j)*(t-s j.castSucc)) := by
    apply prod_nonneg
    intro j hj
    have ne := (mem_erase.mp hj).1
    rcases lt_or_gt_of_ne ne with h|h
    · have sep : s j.succ ≤ s i.castSucc := order (by exact h)
      have lim := ((alt j).2.trans sep).trans left.le
      exact mul_nonneg (sub_nonneg.mpr lim) (sub_nonneg.mpr ((alt j).1.trans lim))
    · have sep : s i.succ ≤ s j.castSucc := order (by exact h)
      have lim := right.le.trans ((alt i).2.trans sep)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (lim.trans (alt j).1)) (sub_nonpos.mpr lim)
  rw [←prod_erase_mul univ (fun j ↦ (t-r j)*(t-s j.castSucc)) (mem_univ i)] at negative
  exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr below.le)
      (mul_nonpos_of_nonneg_of_nonpos others opposite.le))) negative

theorem wronskian_at_opposite_sign {p q : ℝ[X]} (h : WeakRealInterlacing p q)
    (pl : 0 < p.leadingCoeff) (ql : 0 < q.leadingCoeff) (t : ℝ)
    (opp : p.eval t*q.eval t < 0) :
    0 ≤ q.derivative.eval t * p.eval t - p.derivative.eval t * q.eval t := by
  obtain ⟨d,r,s,a,b,_,_,rfl,rfl,_,order,alt⟩ := h
  rw [leadingCoeff_mul,leadingCoeff_C,(factor_monic r).leadingCoeff,mul_one] at pl
  rw [leadingCoeff_mul,leadingCoeff_C,(factor_monic s).leadingCoeff,mul_one] at ql
  let z := fun i : Fin d ↦ s i.castSucc
  have split : linearFactors s = linearFactors z * (X-C (s (Fin.last d))) := by
    unfold linearFactors
    exact Fin.prod_univ_castSucc _
  let v := fun i : Fin d ↦ (t-r i)*(t-z i)
  have geom : (t-s (Fin.last d)) * ∏ i, v i < 0 := by
    apply neg_of_mul_neg_right _ (mul_pos pl ql).le
    rw [split] at opp
    simp only [eval_mul,eval_X,eval_sub,eval_C,factors_at] at opp
    dsimp [v];rw [prod_mul_distrib]
    linarith only [opp]
  obtain ⟨below,allpos⟩ := obstruction_geometry order alt t geom
  have sumneg : (∑ i, (z i-r i)*∏ j ∈ univ.erase i, v j) ≤ 0 :=
    sum_nonpos (fun i _ ↦ mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (alt i).1)
      (prod_nonneg (fun j _ ↦ allpos j)))
  have prodpos : 0 ≤ (linearFactors r).eval t * (linearFactors z).eval t := by
    rw [factors_at,factors_at,←prod_mul_distrib]
    exact prod_nonneg (fun i _ ↦ allpos i)
  have good := add_nonneg prodpos (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr below.le) sumneg)
  rw [←paired_derivative r z t] at good
  rw [split]
  simp only [derivative_mul,derivative_C,zero_mul,zero_add,eval_mul,eval_C,
    derivative_X_sub_C,mul_one,eval_add,eval_X,eval_sub]
  nlinarith only [mul_nonneg (mul_pos pl ql).le good]

#print axioms wronskian_at_opposite_sign
end LongCycleBounds.RootTests
