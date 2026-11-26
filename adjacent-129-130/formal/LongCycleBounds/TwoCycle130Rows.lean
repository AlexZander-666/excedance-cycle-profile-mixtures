import LongCycleBounds.CycleProfile

/-! Two genuine derangement rows on a common binary cycle-length profile.
At these sizes no allowed permutation has three cycles. -/
noncomputable section
namespace LongCycleBounds.TwoCycle130
open Finset Polynomial LongCycles CycleProfile

def keep (a : ℕ) : Bool := decide (87 ≤ a ∨
  (2 ∣ a ∧ ((44 ≤ a ∧ a ≤ 54) ∨ (76 ≤ a ∧ a ≤ 86))))

def weight (a : ℕ) : ℝ := if keep a then 1 else 0

theorem unit (a : ℕ) : weight a ∈ Set.Icc (0:ℝ) 1 := by
  unfold weight;split <;> norm_num

theorem unit_tail (a : ℕ) (h : 87 ≤ a) : weight a=1 := by simp [weight,keep,h]

private theorem minimum {a : ℕ} (h : keep a) : 44 ≤ a := by
  simp only [keep,decide_eq_true_eq] at h;omega

theorem at_most_two {n : ℕ} (bound : n ≤ 130) {σ : Equiv.Perm (Fin n)}
    (live : ∀ a ∈ σ.partition.parts, keep a) : σ.partition.parts.card ≤ 2 := by
  have mass (L : Multiset ℕ) (all : ∀ v ∈ L, 44 ≤ v) : L.card * 44 ≤ L.sum := by
    induction L using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      have low := all a (by simp)
      have rest := ih (fun v hv ↦ all v (by simp [hv]))
      simp only [Multiset.card_cons,Multiset.sum_cons];omega
  have sum_eq : σ.partition.parts.sum = n := σ.partition.parts_sum.trans (Fintype.card_fin n)
  have h := (mass _ (fun v hv ↦ minimum (live v hv))).trans_eq sum_eq
  omega

private theorem row0 : row 0 weight=1 := by
  unfold row
  rw [Fintype.sum_unique]
  have e : (default : Equiv.Perm (Fin 0))=1 := Subsingleton.elim _ _
  simp [e,term,cycleWeight,excedances,Allowed]

private theorem before {n : ℕ} (hn : 0 < n) (low : n < 44) : row n weight=0 := by
  rw [row_anchored (n:=n) ⟨0,hn⟩ weight]
  apply sum_eq_zero
  intro a ha
  have an := (mem_Icc.mp ha).2
  have wk : keep a=false := by
    by_cases ht : keep a = true
    · have := minimum ht;omega
    · simpa using ht
  simp [weight,wk]

private theorem one_cycle {n : ℕ} (hn : 0 < n) (upper : n < 88) :
    row n weight=C (weight n)*(X*eulerian (n-1)) := by
  by_cases h : n < 2
  · rw [before hn (by omega)]
    have eq : n=1 := by omega
    simp [eq,weight,keep]
  rw [row_anchored (n:=n) ⟨0,hn⟩ weight,sum_eq_single_of_mem n (mem_Icc.mpr ⟨by omega,le_rfl⟩)]
  · simp [row0]
  · intro a ha ne
    by_cases use : keep a
    · have aa := minimum use
      have an := (mem_Icc.mp ha).2
      rw [before (by omega : 0 < n-a) (by omega : n-a < 44),mul_zero]
    · simp [weight,use]

private def live (n : ℕ) : Finset ℕ :=
  (Icc 2 n).filter (fun a ↦ keep a ∧ (a=n ∨ keep (n-a)))

private def piece (n a : ℕ) : ℝ[X] :=
  if a=n then X*eulerian (n-1)
  else C ((n-1).choose (a-1):ℝ) * (X*eulerian (a-1)) * (X*eulerian (n-a-1))

private theorem two_cycle_sum {n : ℕ} (hn : 2 ≤ n) (upper : n ≤ 130) :
    row n weight = ∑ a ∈ live n, piece n a := by
  rw [row_anchored (n:=n) ⟨0,by omega⟩ weight,live,sum_filter]
  apply sum_congr rfl
  intro a ha
  have an := (mem_Icc.mp ha).2
  by_cases use : keep a
  · by_cases eq : a=n
    · subst a;simp [weight,use,row0,piece]
    · have amin := minimum use
      rw [one_cycle (by omega : 0 < n-a) (by omega : n-a < 88)]
      by_cases rest : keep (n-a) <;> simp [weight,use,rest,eq,piece]
  · simp [weight,use]

def small : Finset ℕ := {44,46,48,50,52,54}

def blockTerm (n a : ℕ) : ℝ[X] :=
  C (n.choose a : ℝ) * eulerian (a-1) * eulerian (n-1-a)

def upperFormula (n : ℕ) (A : Finset ℕ) : ℝ[X] :=
  eulerian (n-1) + X * ∑ a ∈ A, blockTerm n a

abbrev upperQ := upperFormula 130 small

attribute [local irreducible] eulerian row
set_option maxRecDepth 10000

private theorem singleton_row (n : ℕ) (hn : 2 ≤ n) (hi : n ≤ 130) (one : live n={n}) :
    row n weight = X * eulerian (n-1) := by
  rw [two_cycle_sum hn hi,one,sum_singleton,piece,if_pos rfl]

private theorem live129 : live 129={129} := by
  ext a;simp [live,keep];omega

theorem lower_row : row 129 weight = X * eulerian (129-1) :=
  singleton_row 129 (by decide) (by decide) live129

private theorem grouped (f : ℕ → ℝ[X]) :
    (∑ a ∈ live 130, f a) = f 130 + ∑ a ∈ small, (f a + f (130-a)) := by
  rw [show live 130={44,46,48,50,52,54,76,78,80,82,84,86,130} by ext a;simp [live,keep];omega]
  unfold small
  norm_num [sum_insert]
  ring

private theorem pair {a : ℕ} (ha : a ∈ small) :
    piece 130 a + piece 130 (130-a) =
    X * (X * blockTerm 130 a) := by
  unfold blockTerm
  have bounds : small ⊆ Icc 44 54 := by intro i hi;simp [small] at hi;rw [mem_Icc];omega
  obtain ⟨lo,hi⟩ := mem_Icc.mp (bounds ha)
  have comb : (130:ℕ).choose a = (129:ℕ).choose (a-1) + (129:ℕ).choose (129-a) := by
    rw [Nat.choose_symm (by omega : a ≤ 129)]
    convert Nat.choose_succ_succ 129 (a-1) using 1 <;> rw [show (a-1).succ=a by omega]
  simp only [piece,if_neg (by omega : a ≠ 130),if_neg (by omega : 130-a ≠ 130),
    show 130-(130-a)=a by omega,show 130-a-1=129-a by omega,show 130-1=129 by decide,
    comb, Nat.cast_add, map_add]
  ring

private theorem assemble {n : ℕ} (hn : 2 ≤ n) (hi : n ≤ 130) (A : Finset ℕ)
    (group : (∑ a ∈ live n, piece n a) =
      piece n n + ∑ a ∈ A, (piece n a + piece n (n-a)))
    (combine : ∀ a ∈ A, piece n a + piece n (n-a) = X * (X * blockTerm n a)) :
    row n weight = X * upperFormula n A := by
  unfold upperFormula
  rw [two_cycle_sum hn hi,group,sum_congr rfl combine]
  rw [show piece n n = X * eulerian (n-1) from if_pos rfl]
  rw [mul_add,mul_sum,mul_sum]

private theorem group130 :
    (∑ a ∈ live 130, piece 130 a) =
      piece 130 130 + ∑ a ∈ small, (piece 130 a + piece 130 (130-a)) := grouped (piece 130)

private theorem combine130 : ∀ a ∈ small,
    piece 130 a + piece 130 (130-a) = X * (X * blockTerm 130 a) := fun _ ha ↦ pair ha

theorem upper_row : row 130 weight = X * upperFormula 130 small :=
  @assemble 130 (by decide) (by decide) small group130 combine130

#print axioms at_most_two
#print axioms lower_row
#print axioms upper_row
end LongCycleBounds.TwoCycle130
