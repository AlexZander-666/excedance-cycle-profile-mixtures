import LongCycleBounds.DescentItineraryInventory
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn

/-! Encoding a sorted inventory by its multiplicity at each rooted cyclic word. -/
noncomputable section
namespace LongCycleBounds.DescentNecklace

section General
variable {n : ℕ} {K : Type*} [LinearOrder K] [Fintype K]

omit [Fintype K] in
theorem frequency_count (w : Fin n → K) (s : K) :
    frequency w s = (List.ofFn w : Multiset K).count s := by
  rw [← Fin.univ_val_map,Multiset.count_map,frequency,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp [Finset.card,Finset.filter_val,eq_comm]

def expand (m : K → ℕ) : Multiset K := ∑ s, Multiset.replicate (m s) s

@[simp] theorem expand_count (m : K → ℕ) (s : K) : (expand m).count s = m s := by
  simp [expand,Multiset.count_sum',Multiset.count_replicate]

omit [LinearOrder K] in
@[simp] theorem expand_card (m : K → ℕ) : (expand m).card = ∑ s, m s := by
  simp [expand,Multiset.card_sum]

theorem expand_frequency (w : Fin n → K) : expand (frequency w) = List.ofFn w := by
  ext s
  rw [expand_count,frequency_count]

theorem total_frequency (w : Fin n → K) : ∑ s, frequency w s = n := by
  rw [← expand_card,expand_frequency]
  simp

theorem sorted_determined {w v : Fin n → K} (hw : Monotone w) (hv : Monotone v)
    (eq : frequency w = frequency v) : w = v := by
  apply List.ofFn_injective
  apply List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hw) (List.sortedLE_ofFn_iff.mpr hv)
  apply Multiset.coe_eq_coe.mp
  rw [← expand_frequency w,← expand_frequency v,eq]

def enumerateMass (m : K → ℕ) (h : ∑ s, m s = n) : Fin n → K :=
  let l := (expand m).sort (· ≤ ·)
  fun i ↦ l.get (Fin.cast (by simpa [l] using h.symm) i)

theorem enumerate_list (m : K → ℕ) (h : ∑ s, m s = n) :
    List.ofFn (enumerateMass m h) = (expand m).sort (· ≤ ·) := by
  let l := (expand m).sort (· ≤ ·)
  have len : l.length = n := by simpa [l] using h
  exact (List.ofFn_congr len l.get).symm.trans (List.ofFn_get l)

theorem enumerate_monotone (m : K → ℕ) (h : ∑ s, m s = n) : Monotone (enumerateMass m h) := by
  rw [← List.sortedLE_ofFn_iff,enumerate_list]
  exact List.sortedLE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)

theorem enumerate_frequency (m : K → ℕ) (h : ∑ s, m s = n) : frequency (enumerateMass m h) = m := by
  funext s
  rw [frequency_count,enumerate_list,Multiset.sort_eq,expand_count]

end General

variable {n q : ℕ}

theorem frequency_pos_iff {K : Type*} [DecidableEq K] (w : Fin n → K) (s : K) :
    0 < frequency w s ↔ ∃ i, w i = s := by
  rw [frequency,Nat.card_eq_fintype_card,Fintype.card_pos_iff]
  exact ⟨fun ⟨i,h⟩ ↦ ⟨i,h⟩, fun ⟨i,h⟩ ↦ ⟨⟨i,h⟩⟩⟩

/-- Multiplicities are constant around an orbit and vanish below the prescribed period. -/
def MassInventory (n q k : ℕ) :=
  {m : Key n q → ℕ // (∑ s, m s) = n ∧ (∀ s, m (turn n q s) = m s) ∧
    ∀ s, 0 < m s → k ≤ LongCycleBounds.Necklace.period (ofLex s)}

def massEquiv (n q k : ℕ) :
    {w : OrderedInventory n q // ∀ i, k ≤ LongCycleBounds.Necklace.period (ofLex (w.val i))} ≃
      MassInventory n q k where
  toFun w := ⟨frequency w.val.val,total_frequency (K := Key n q) w.val.val,w.val.property.2,
    fun s hs ↦ by obtain ⟨i,rfl⟩ := (frequency_pos_iff w.val.val s).mp hs; exact w.property i⟩
  invFun m := by
    let w := enumerateMass m.val m.property.1
    have freq : frequency w = m.val := enumerate_frequency _ _
    refine ⟨⟨w,enumerate_monotone _ _,?_⟩,?_⟩
    · rw [freq]
      exact m.property.2.1
    · intro i
      apply m.property.2.2
      exact lt_of_lt_of_eq ((frequency_pos_iff w (w i)).mpr ⟨i,rfl⟩) (congrFun freq (w i))
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact sorted_determined (enumerate_monotone (frequency w.val.val) (total_frequency w.val.val))
      w.val.property.1 (enumerate_frequency (frequency w.val.val) (total_frequency w.val.val))
  right_inv m := by
    apply Subtype.ext
    exact enumerate_frequency m.val m.property.1

def cutoffMassEquiv (n q k : ℕ) :
    {u : Compatible n q // LongCycles.Allowed k u.val.1} ≃ MassInventory n q k :=
  (cutoffInventoryEquiv n q k).trans (massEquiv n q k)

#print axioms cutoffMassEquiv
end LongCycleBounds.DescentNecklace
