import LongCycleBounds.InterlacingWronskian

namespace LongCycleBounds.RootTests
open Polynomial LongCycles

/-- A common factor X preserves the sign of the Wronskian away from zero.
The four quotient signs suffice without counting or isolating any roots. -/
theorem common_zero_obstruction {p q P Q : ℝ[X]} (fp : p=X*P) (fq : q=X*Q)
    (pl : 0 < p.leadingCoeff) (ql : 0 < q.leadingCoeff) {t : ℝ} (t0 : t ≠ 0)
    (valP : P.eval t < 0) (valQ : 0 < Q.eval t)
    (derP : 0 < P.derivative.eval t) (derQ : 0 < Q.derivative.eval t) :
    ¬WeakRealInterlacing p q := by
  intro h
  have tsq := sq_pos_of_ne_zero t0
  have k := mul_neg_of_pos_of_neg tsq (mul_neg_of_neg_of_pos valP valQ)
  have opposite : p.eval t * q.eval t < 0 := by
    rw [fp,fq,eval_mul,eval_mul,eval_X]
    nlinarith only [k]
  have good := wronskian_at_opposite_sign h pl ql t opposite
  have bad := mul_neg_of_pos_of_neg tsq (sub_neg.mpr
    ((mul_neg_of_pos_of_neg derQ valP).trans (mul_pos derP valQ)))
  rw [fp,fq] at good
  simp only [derivative_mul,derivative_X,one_mul,eval_mul,eval_X,eval_add] at good
  nlinarith only [good,bad]

#print axioms common_zero_obstruction
end LongCycleBounds.RootTests
