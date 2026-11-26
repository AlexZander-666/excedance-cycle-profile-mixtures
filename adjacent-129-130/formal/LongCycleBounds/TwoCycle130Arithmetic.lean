import LongCycleFinite.CoefficientRows

/-! Exact signs of the two degree-127 and degree-128 quotient rows at a rational point. -/

namespace LongCycleBounds.TwoCycle130Arithmetic

open Polynomial LongCycleFinite
attribute [local irreducible] descentCoeffs

/-- Possible shorter lengths in the permitted two-cycle decompositions of the upper row. -/
def splitSizes : Finset ℕ := {44, 46, 48, 50, 52, 54}

/-- The ascending coefficients of the lower quotient. -/
def lowerCoeffs : List ℤ := descentCoeffs 128

private def splitTerm (a : ℕ) : List ℤ :=
  scaleCoeffs (Nat.fast_choose 130 a : ℤ)
    (mulCoeffs (descentCoeffs (a - 1)) (descentCoeffs (129 - a)))

private def sumSplits : List ℕ → List ℤ
  | [] => []
  | a :: as => addCoeffs (splitTerm a) (sumSplits as)

/-- The ascending coefficients of the upper quotient, with the compound terms multiplied by X. -/
def upperCoeffs : List ℤ :=
  addCoeffs (descentCoeffs 129) (0 :: sumSplits [44, 46, 48, 50, 52, 54])

theorem lowerCoeffs_spec : ofCoeffs lowerCoeffs = LongCycles.eulerian 128 :=
  ofCoeffs_descentCoeffs 128

private noncomputable def splitPolynomial (a : ℕ) : Polynomial ℝ :=
  C ((130 : ℕ).choose a : ℝ) * LongCycles.eulerian (a - 1) * LongCycles.eulerian (129 - a)

private theorem ofCoeffs_splitTerm (a : ℕ) : ofCoeffs (splitTerm a) = splitPolynomial a := by
  rw [splitTerm, ofCoeffs_scaleCoeffs, ofCoeffs_mulCoeffs, ofCoeffs_descentCoeffs,
    ofCoeffs_descentCoeffs, splitPolynomial, Nat.choose_eq_fast_choose, Int.cast_natCast, mul_assoc]

private theorem ofCoeffs_sumSplits (as : List ℕ) :
    ofCoeffs (sumSplits as) = (as.map splitPolynomial).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [sumSplits, ofCoeffs_addCoeffs, ofCoeffs_splitTerm, ih, List.map_cons, List.sum_cons]

private theorem ofCoeffs_upper_formula (n : ℕ) (as : List ℕ) :
    ofCoeffs (addCoeffs (descentCoeffs n) (0 :: sumSplits as)) =
      LongCycles.eulerian n + X * (as.map splitPolynomial).sum := by
  rw [ofCoeffs_addCoeffs, ofCoeffs_descentCoeffs]
  rw [ofCoeffs, Int.cast_zero, C_0, zero_add, ofCoeffs_sumSplits]

private theorem upper_coefficients_of_distinct_splits (n : ℕ) (as : List ℕ) (ha : as.Nodup) :
    ofCoeffs (addCoeffs (descentCoeffs n) (0 :: sumSplits as)) =
      LongCycles.eulerian n + X * ∑ a ∈ as.toFinset,
        C ((130 : ℕ).choose a : ℝ) * LongCycles.eulerian (a - 1) *
          LongCycles.eulerian (129 - a) := by
  rw [ofCoeffs_upper_formula]
  exact congrArg (fun q : Polynomial ℝ ↦ LongCycles.eulerian n + X * q)
    (List.sum_toFinset splitPolynomial ha).symm

theorem upperCoeffs_spec :
    ofCoeffs upperCoeffs = LongCycles.eulerian 129 + X *
      ∑ a ∈ splitSizes, C ((130 : ℕ).choose a : ℝ) *
        LongCycles.eulerian (a - 1) * LongCycles.eulerian (129 - a) := by
  have hf : ([44, 46, 48, 50, 52, 54] : List ℕ).toFinset = splitSizes := by decide
  rw [← hf, upperCoeffs]
  exact upper_coefficients_of_distinct_splits 129 [44, 46, 48, 50, 52, 54] (by decide)

private def denominator : ℕ := 9800000000000000

/-- The exact rational evaluation point of this witness. -/
noncomputable def point : ℝ := -1 / (denominator : ℝ)

/-- The denominator power, value numerator and derivative numerator at minus the reciprocal
of the denominator. Both numerators have the same scaling. -/
private def scaledJet (d : ℕ) : List ℤ → ℤ × ℤ × ℤ
  | [] => (1, 0, 0)
  | a :: as =>
      let tail := scaledJet d as
      let scale := (d : ℤ) * tail.1
      (scale, a * scale - tail.2.1, (d : ℤ) * tail.2.1 - tail.2.2)

private theorem scaledJet_spec (d : ℕ) (hd : 0 < d) (cs : List ℤ) :
    let b := (d : ℝ)
    let J := scaledJet d cs
    (J.1 : ℝ) = b^cs.length ∧
      (J.2.1 : ℝ) = b^cs.length * (ofCoeffs cs).eval (-1 / b) ∧
      (J.2.2 : ℝ) = b^cs.length * (ofCoeffs cs).derivative.eval (-1 / b) := by
  have hn : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  induction cs with
  | nil => simp [scaledJet, ofCoeffs]
  | cons a as ih =>
    obtain ⟨hp, hv, hs⟩ := ih
    simp only [scaledJet, List.length_cons, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
      ofCoeffs, eval_add, eval_C, eval_mul, eval_X, derivative_add, derivative_C, derivative_mul,
      derivative_X, zero_add, one_mul, pow_succ, hp, hv, hs]
    refine ⟨by ring, ?_, ?_⟩ <;> field_simp <;> ring

private def checkSigns (negative : Bool) (cs : List ℤ) : Bool :=
  let jet := scaledJet denominator cs
  (if negative then decide (jet.2.1 < 0) else decide (0 < jet.2.1)) &&
    decide (0 < jet.2.2)

private theorem checkSigns_sound (negative : Bool) (cs : List ℤ)
    (h : checkSigns negative cs = true) :
    (if negative then (ofCoeffs cs).eval point < 0 else 0 < (ofCoeffs cs).eval point) ∧
      0 < (ofCoeffs cs).derivative.eval point := by
  have dpos : 0 < denominator := by decide
  have scale : 0 < (denominator : ℝ)^cs.length := by positivity
  obtain ⟨_, hv, hs⟩ := scaledJet_spec denominator dpos cs
  change ((scaledJet denominator cs).2.1 : ℝ) =
    (denominator : ℝ)^cs.length * (ofCoeffs cs).eval point at hv
  change ((scaledJet denominator cs).2.2 : ℝ) =
    (denominator : ℝ)^cs.length * (ofCoeffs cs).derivative.eval point at hs
  cases negative
  · simp only [checkSigns, Bool.false_eq_true, if_false, Bool.and_eq_true,
      decide_eq_true_eq] at h
    have hv' : (0 : ℝ) < ((scaledJet denominator cs).2.1 : ℝ) := by exact_mod_cast h.1
    have hs' : (0 : ℝ) < ((scaledJet denominator cs).2.2 : ℝ) := by exact_mod_cast h.2
    exact ⟨(mul_pos_iff_of_pos_left scale).mp (hv ▸ hv'),
      (mul_pos_iff_of_pos_left scale).mp (hs ▸ hs')⟩
  · simp only [checkSigns, if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    have hv' : ((scaledJet denominator cs).2.1 : ℝ) < 0 := by exact_mod_cast h.1
    have hs' : (0 : ℝ) < ((scaledJet denominator cs).2.2 : ℝ) := by exact_mod_cast h.2
    have hneg := (mul_neg_iff.mp (hv ▸ hv')).resolve_right
      (fun pair ↦ (not_lt_of_ge scale.le) pair.1)
    exact ⟨hneg.2, (mul_pos_iff_of_pos_left scale).mp (hs ▸ hs')⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem lower_check : checkSigns true lowerCoeffs = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem upper_check : checkSigns false upperCoeffs = true := by decide +kernel

/-- The exact four inequalities at the rational witness point. -/
theorem evaluated_signs :
    (ofCoeffs lowerCoeffs).eval point < 0 ∧ 0 < (ofCoeffs upperCoeffs).eval point ∧
      0 < (ofCoeffs lowerCoeffs).derivative.eval point ∧
      0 < (ofCoeffs upperCoeffs).derivative.eval point := by
  obtain ⟨lv, ld⟩ := checkSigns_sound true lowerCoeffs lower_check
  obtain ⟨uv, ud⟩ := checkSigns_sound false upperCoeffs upper_check
  exact ⟨lv, uv, ld, ud⟩

#print axioms lowerCoeffs_spec
#print axioms upperCoeffs_spec
#print axioms evaluated_signs

end LongCycleBounds.TwoCycle130Arithmetic
