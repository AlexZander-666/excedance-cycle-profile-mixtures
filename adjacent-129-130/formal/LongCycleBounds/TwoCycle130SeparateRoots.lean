import LongCycleBounds.TwoCycle130Verified
import LongCycleBounds.TwoCycle130RootData

/-! The two actual rows have simple real zeros individually and fail interlacing as a pair. -/
namespace LongCycleBounds.TwoCycle130
open LongCycles Polynomial LongCycleFinite CycleProfile DescentNecklace
open TwoCycle130Arithmetic TwoCycle130RootData
set_option maxRecDepth 24000

def SimpleRow (p : ℝ[X]) (d : ℕ) : Prop :=
  p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.roots.card = d+1 ∧
  (p.roots.filter (· < 0)).card = d

private theorem of_mesh {c : List ℤ} {nodes : Array LongCycleFinite.Dyadic} {d : ℕ}
    (h : negativeMeshOK c nodes = true) (size : nodes.size - 1 = d) :
    SimpleRow (X * ofCoeffs c) d := by
  obtain ⟨m⟩ := negativeMeshOK_sound h
  subst d
  exact m.full_root_count

private theorem expand_upper (n : ℕ) (A : Finset ℕ) :
    upperFormula n A = eulerian (n-1) + X *
      ∑ a ∈ A, C (n.choose a : ℝ) * eulerian (a-1) * eulerian (n-1-a) := rfl

attribute [local irreducible] eulerian upperCoeffs

private theorem upper_identification : ofCoeffs upperCoeffs = upperQ := by
  unfold upperQ
  rw [expand_upper, show 130 - 1 = (129 : ℕ) by rfl, show small = splitSizes by rfl]
  exact upperCoeffs_spec

theorem lower_simple : SimpleRow (row 129 weight) 127 := by
  have h : row 129 weight = X * ofCoeffs lowerCoeffs :=
    lower_row.trans (congrArg (fun p : ℝ[X] ↦ X*p) lowerCoeffs_spec.symm)
  rw [h]
  exact of_mesh lowerMesh (by decide)

theorem upper_simple : SimpleRow (row 130 weight) 128 := by
  have h : row 130 weight = X * ofCoeffs upperCoeffs :=
    upper_row.trans (congrArg (fun p : ℝ[X] ↦ X*p) upper_identification.symm)
  rw [h]
  exact of_mesh upperMesh (by decide)

theorem individually_real_but_not_interlacing :
    SimpleRow (row 129 weight) 127 ∧ SimpleRow (row 130 weight) 128 ∧
    ¬ WeakRealInterlacing (row 129 weight) (row 130 weight) :=
  ⟨lower_simple, upper_simple, original_not_interlacing⟩

#print axioms individually_real_but_not_interlacing
end LongCycleBounds.TwoCycle130
