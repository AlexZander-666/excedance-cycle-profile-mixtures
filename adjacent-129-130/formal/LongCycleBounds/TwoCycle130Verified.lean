import LongCycleBounds.TwoCycle130Rows
import LongCycleBounds.TwoCycle130Arithmetic
import LongCycleBounds.CycleProfileIndependentWeights
import LongCycleBounds.CommonZeroWronskian

/-! A single admissible binary profile with an unrestricted tail from 87.
Its genuine strict-excedance rows at 129 and 130 fail weak interlacing. -/
namespace LongCycleBounds.TwoCycle130
open LongCycles Polynomial CycleProfile LongCycleFinite

/-- Every derangement with nonzero weight in either actual row has at most
two cycles, counted in its full cycle partition. -/
theorem nonzero_weight_at_most_two {n : ℕ} (hn : n ≤ 130) {σ : Equiv.Perm (Fin n)}
    (allowed : Allowed 2 σ) (nz : cycleWeight weight σ ≠ 0) : σ.partition.parts.card ≤ 2 := by
  apply at_most_two hn
  intro a hi
  rw [Equiv.Perm.parts_partition,support_univ_of_allowed allowed (by decide)] at hi
  simp only [Finset.card_univ,Nat.sub_self,Multiset.replicate_zero,add_zero] at hi
  by_contra bad
  apply nz
  apply Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨a,hi,?_⟩)
  simp [weight,bad]

private theorem lc_pos (n : ℕ) (hn : 87 ≤ n) : 0 < (row n weight).leadingCoeff := by
  obtain ⟨_,mon,_,factor⟩ := weightedQuotient_shape (by decide : 2 ≤ 87) hn unit unit_tail
  rw [factor,leadingCoeff_mul,leadingCoeff_X,mon.leadingCoeff]
  norm_num

private theorem expand_formula (n : ℕ) (A : Finset ℕ) :
    upperFormula n A = eulerian (n-1) + X *
      ∑ a ∈ A, C (n.choose a : ℝ) * eulerian (a-1) * eulerian (n-1-a) := rfl

private theorem lower_base_index : 130 - 1 = (129 : ℕ) := rfl

private theorem explicit_splits : small = TwoCycle130Arithmetic.splitSizes := rfl

attribute [local irreducible] eulerian TwoCycle130Arithmetic.upperCoeffs
private theorem upper_arithmetic : ofCoeffs TwoCycle130Arithmetic.upperCoeffs = upperQ := by
  unfold upperQ
  rw [expand_formula, lower_base_index, explicit_splits]
  exact TwoCycle130Arithmetic.upperCoeffs_spec

private theorem lower_physical : row 129 weight = X * ofCoeffs TwoCycle130Arithmetic.lowerCoeffs :=
  lower_row.trans (congrArg (fun p : ℝ[X] ↦ X*p) TwoCycle130Arithmetic.lowerCoeffs_spec.symm)

private theorem upper_physical : row 130 weight = X * ofCoeffs TwoCycle130Arithmetic.upperCoeffs :=
  upper_row.trans (congrArg (fun p : ℝ[X] ↦ X*p) upper_arithmetic.symm)

theorem original_not_interlacing : ¬WeakRealInterlacing (row 129 weight) (row 130 weight) := by
  have t0 : TwoCycle130Arithmetic.point ≠ 0 := by change (-1:ℝ)/(9800000000000000:ℝ) ≠ 0;norm_num
  obtain ⟨hp,hq,dp,dq⟩ := TwoCycle130Arithmetic.evaluated_signs
  exact RootTests.common_zero_obstruction lower_physical upper_physical (lc_pos _ (by decide))
    (lc_pos _ (by decide)) t0 hp hq dp dq

#print axioms nonzero_weight_at_most_two
#print axioms original_not_interlacing
end LongCycleBounds.TwoCycle130
