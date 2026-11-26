import LongCycleBounds.DescentPrimitiveItinerary
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Hom.Set

/-! Stable standardization of finite words using the original ordinary descent convention. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace
open LongCycles LongCycleBounds.DescentMesh

variable {n q : ℕ}

def Stable (σ : Equiv.Perm (Fin n)) (x : Fin n → Fin q) : Prop :=
  StrictMono fun i ↦ toLex (x i, σ i)

theorem stable_iff_adjacent {m : ℕ} (σ : Equiv.Perm (Fin (m+1))) (x : Fin (m+1) → Fin q) :
    Stable σ x ↔ Monotone x ∧
      ∀ i : Fin m, σ i.succ < σ i.castSucc → x i.castSucc < x i.succ := by
  constructor
  · intro h
    refine ⟨monotone_iff_forall_lt.mpr (fun a b ab ↦ (Prod.Lex.toLex_lt_toLex'.mp (h ab)).1),?_⟩
    intro i desc
    obtain ⟨hle,tie⟩ := Prod.Lex.toLex_lt_toLex'.mp (h (Fin.castSucc_lt_succ (i := i)))
    exact lt_of_le_of_ne hle (fun eq ↦ (tie eq).not_gt desc)
  · rintro ⟨mono,rise⟩ a b hab
    exact Prod.Lex.toLex_lt_toLex'.mpr ⟨mono hab.le,order_of_equal_color σ x mono rise hab⟩

abbrev Position (w : Fin n → Fin q) :=
  {u : Fin q ×ₗ Fin n // (ofLex u).1 = w (ofLex u).2}

def seat (w : Fin n → Fin q) : Fin n ≃ Position w where
  toFun i := ⟨toLex (w i,i),rfl⟩
  invFun u := (ofLex u.val).2
  left_inv _ := rfl
  right_inv u := by
    apply Subtype.ext
    apply ofLex.injective
    exact Prod.ext u.property.symm rfl

def sorted (w : Fin n → Fin q) : Fin n ≃o Position w :=
  Fintype.orderIsoFinOfCardEq (Position w) (by rw [Fintype.card_congr (seat w).symm,Fintype.card_fin])

def standardize (w : Fin n → Fin q) : Equiv.Perm (Fin n) :=
  (sorted w).toEquiv.trans (seat w).symm

def colors (w : Fin n → Fin q) : Fin n → Fin q := w ∘ standardize w

private theorem sorted_value (w : Fin n → Fin q) (i : Fin n) :
    (sorted w i).val = toLex (colors w i,standardize w i) := by
  change (sorted w i).val = toLex (w (ofLex (sorted w i).val).2,(ofLex (sorted w i).val).2)
  apply ofLex.injective
  exact Prod.ext (sorted w i).property rfl

theorem standardize_stable (w : Fin n → Fin q) : Stable (standardize w) (colors w) := by
  intro a b ab
  change toLex (colors w a, standardize w a) < toLex (colors w b, standardize w b)
  rw [←sorted_value,←sorted_value]
  exact (sorted w).strictMono ab

theorem stable_unique (w : Fin n → Fin q) (σ : Equiv.Perm (Fin n))
    (h : Stable σ (w ∘ σ)) : σ = standardize w := by
  let e := σ.trans (seat w)
  have he : StrictMono e := by
    intro a b ab
    exact h ab
  let o := he.orderIsoOfRightInverse e e.symm e.apply_symm_apply
  have same : o = sorted w := Subsingleton.elim _ _
  apply Equiv.ext
  intro i
  have hi := congrArg (fun f : Fin n ≃o Position w ↦ (seat w).symm (f i)) same
  change (seat w).symm (seat w (σ i)) = standardize w i at hi
  simpa only [Equiv.symm_apply_apply] using hi

abbrev Compatible (n q : ℕ) := {p : Equiv.Perm (Fin n) × (Fin n → Fin q) // Stable p.1 p.2}

/-- All words are in bijection with permutations equipped with weakly increasing
labels which rise at each ordinary descent. The inverse word is written in original positions. -/
def wordEquiv (n q : ℕ) : (Fin n → Fin q) ≃ Compatible n q where
  toFun w := ⟨(standardize w,colors w),standardize_stable w⟩
  invFun u := u.val.2 ∘ u.val.1.symm
  left_inv w := by funext i; exact congrArg w ((standardize w).apply_symm_apply i)
  right_inv u := by
    obtain ⟨⟨σ,x⟩,h⟩ := u
    let w := x ∘ σ.symm
    have orig : w ∘ σ = x := by funext i; simp [w]
    have he : σ = standardize w := stable_unique w σ (orig ▸ h)
    apply Subtype.ext
    exact Prod.ext he.symm (show colors w = x by unfold colors; rw [←he,orig])

/-- Equal initial colors preserve order until the first place at which itineraries differ. -/
theorem prefix_preserves_order {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) {a b : Fin n} (ab : a < b) (j : ℕ)
    (same : ∀ i < j, x ((σ ^ i) a) = x ((σ ^ i) b)) : (σ ^ j) a < (σ ^ j) b := by
  induction j with
  | zero => simpa using ab
  | succ j ih =>
    have h := (Prod.Lex.toLex_lt_toLex'.mp (st (ih (fun i hi ↦ same i (Nat.lt_succ_of_lt hi))))).2
      (same j (Nat.lt_succ_self j))
    simpa [pow_succ', Equiv.Perm.mul_apply] using h

/-- At a first unequal letter the original order and the letter order agree, in both directions. -/
theorem first_difference_iff {σ : Equiv.Perm (Fin n)} {x : Fin n → Fin q}
    (st : Stable σ x) (a b : Fin n) (j : ℕ)
    (same : ∀ i < j, x ((σ ^ i) a) = x ((σ ^ i) b))
    (diff : x ((σ ^ j) a) ≠ x ((σ ^ j) b)) :
    a < b ↔ x ((σ ^ j) a) < x ((σ ^ j) b) := by
  constructor
  · intro ab
    exact lt_of_le_of_ne (Prod.Lex.toLex_lt_toLex'.mp (st (prefix_preserves_order st ab j same))).1 diff
  · intro hab
    rcases lt_trichotomy a b with ab | eq | ba
    · exact ab
    · subst b
      exact False.elim (diff rfl)
    · exact False.elim (hab.not_ge (Prod.Lex.toLex_lt_toLex'.mp
        (st (prefix_preserves_order st ba j (fun i hi ↦ (same i hi).symm)))).1)

#print axioms first_difference_iff
#print axioms stable_iff_adjacent
#print axioms stable_unique
#print axioms wordEquiv
end LongCycleBounds.DescentNecklace
