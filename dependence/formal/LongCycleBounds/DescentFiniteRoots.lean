import LongCycleBounds.DescentNecklaceDP
import LongCycleBounds.DescentNumeratorTransform
import LongCycleFinite.CoefficientRows
import LongCycleFinite.Interlacing
import LongCycleFinite.K3NaturalArithmetic

/-! Exact finite real-root certificates for ordinary descent rows. -/

namespace LongCycleBounds.DescentNecklace

open Polynomial Finset LongCycles LongCycleFinite
open scoped Classical

/-- Cache all alphabet sizes needed by the degree-n numerator inversion. -/
def descentAlphabetTable (n k : ℕ) : Array ℕ :=
  Array.ofFn fun r : Fin n ↦ positiveCountDP n (r.val + 1) k

/-- Determine one coefficient from the cached positive counts. -/
def descentNumeratorCell (n r : ℕ) (letters : Array ℕ) : ℤ :=
  ((List.range (r + 1)).map fun a ↦
    (-1 : ℤ)^a * Nat.fast_choose (n + 1) a * letters.getD (r - a) 0).sum

/-- The exact integer numerator, in ascending order, with length n. -/
def descentRowDP (n k : ℕ) : List ℤ :=
  let letters := descentAlphabetTable n k
  List.ofFn fun r : Fin n ↦ descentNumeratorCell n r.val letters

private theorem alphabetTable_at {n r : ℕ} (h : r < n) (k : ℕ) :
    (descentAlphabetTable n k).getD r 0 = positiveCountDP n (r + 1) k := by
  unfold descentAlphabetTable
  let f (j : Fin n) := positiveCountDP n (j.val + 1) k
  change (Array.ofFn f).getD r 0 = _
  have hr : r < (Array.ofFn f).size := by simpa using h
  rw [Array.getD, dif_pos hr]
  change (Array.ofFn f)[r]'hr = _
  rw [Array.getElem_ofFn]

theorem descentNumeratorCell_correct {n r : ℕ} (hn : 0 < n) (hr : r < n) (k : ℕ) :
    descentNumeratorCell n r (descentAlphabetTable n k) =
      (DescentTwoLetters.row n k).coeff r := by
  unfold descentNumeratorCell
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  rw [coeff_row_from_necklaces hn hr k]
  apply sum_congr rfl
  intro a _
  have h : r - a < n := (Nat.sub_le r a).trans_lt hr
  rw [alphabetTable_at h, card_necklaceContent_eq_positiveCountDP, ← Nat.choose_eq_fast_choose]

private theorem row_coeff_zero_past {n r : ℕ} (hn : 0 < n) (hr : n ≤ r) (k : ℕ) :
    (DescentTwoLetters.row n k).coeff r = 0 := by
  rw [DescentTwoLetters.coeff_row]
  apply sum_eq_zero
  intro σ _
  apply if_neg
  rintro ⟨_, eq⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have bound : descents σ ≤ m := by
    rw [DescentTwoLetters.descents_eq_card]
    exact (card_filter_le _ _).trans_eq (by simp)
  omega

/-- The DP list represents the real form of the original descent row. -/
theorem ofCoeffs_descentRowDP {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ofCoeffs (descentRowDP n k) = (DescentTwoLetters.row n k).map (Int.castRingHom ℝ) := by
  ext r
  rw [coeff_ofCoeffs, coeff_map]
  by_cases hr : r < n
  · let f (i : Fin n) := descentNumeratorCell n i.val (descentAlphabetTable n k)
    change ((List.ofFn f)[r]?.getD 0 : ℝ) = _
    have hl : r < (List.ofFn f).length := by simpa using hr
    rw [List.getElem?_eq_getElem hl, List.getElem_ofFn]
    change (descentNumeratorCell n r (descentAlphabetTable n k) : ℝ) = _
    rw [descentNumeratorCell_correct hn hr]
    rfl
  · have hl : (descentRowDP n k).length ≤ r := by simpa [descentRowDP] using Nat.le_of_not_gt hr
    rw [List.getElem?_eq_none hl, row_coeff_zero_past hn (Nat.le_of_not_gt hr)]
    simp

private theorem ofCoeffs_append_zero (cs : List ℤ) : ofCoeffs (cs ++ [0]) = ofCoeffs cs := by
  induction cs with
  | nil => simp [ofCoeffs]
  | cons a tail ih => simp [ofCoeffs, ih]

/-- A checked coefficient list reads the original real row as X times its quotient. -/
theorem row_eq_of_checkedCoeffs {n k : ℕ} (hn : 0 < n) {cs : List ℤ}
    (checked : descentRowDP n k = (0 :: cs) ++ [0]) :
    (DescentTwoLetters.row n k).map (Int.castRingHom ℝ) = X * ofCoeffs cs := by
  rw [← ofCoeffs_descentRowDP hn k, checked, ofCoeffs_append_zero]
  simp [ofCoeffs]

private def meshNode (nodes : Array LongCycleFinite.Dyadic) (i : ℕ) : LongCycleFinite.Dyadic :=
  nodes.getD i LongCycleFinite.Dyadic.zero

private def meshNegative (last i : ℕ) : Bool := decide ((last - i) % 2 = 1)

private theorem meshNegative_next {last i : ℕ} (h : i < last) :
    meshNegative last (i + 1) = !meshNegative last i := by
  unfold meshNegative
  by_cases odd : (last - i) % 2 = 1
  · have even : (last - (i + 1)) % 2 ≠ 1 := by omega
    simp [odd, even]
  · have next : (last - (i + 1)) % 2 = 1 := by omega
    simp [odd, next]

/-- The quotient signs alternate from left to right and finish positive. -/
def negativeMeshOK (cs : List ℤ) (nodes : Array LongCycleFinite.Dyadic) : Bool :=
  decide (nodes.size = cs.length) &&
  K3.naturalSign false cs LongCycleFinite.Dyadic.zero &&
  (List.range nodes.size).all (fun i ↦
    (meshNode nodes i).less LongCycleFinite.Dyadic.zero &&
      K3.naturalSign (meshNegative (nodes.size - 1) i) cs (meshNode nodes i)) &&
  (List.range (nodes.size - 1)).all (fun i ↦ (meshNode nodes i).less (meshNode nodes (i + 1)))

noncomputable section

/-- Ordered quotient roots and a factorization using every one of them exactly once. -/
structure QuotientMeshRoots (p : ℝ[X]) (nodes : Array LongCycleFinite.Dyadic) (d : ℕ) where
  point : Fin d → ℝ
  positiveAtZero : 0 < p.eval 0
  degreeBound : p.natDegree ≤ d
  ordered : StrictMono point
  negative : ∀ i, point i < 0
  roots : ∀ i, p.eval (point i) = 0
  located : ∀ i, (meshNode nodes i.val).value < point i ∧
    point i < (meshNode nodes (i.val + 1)).value
  factor : p = C p.leadingCoeff * ∏ i, (X - C (point i))

private theorem oppositeSigns {b : Bool} {a c : ℝ}
    (ha : HasSign b a) (hc : HasSign (!b) c) : a * c < 0 := by
  cases b
  · exact mul_neg_of_pos_of_neg ha hc
  · exact mul_neg_of_neg_of_pos ha hc

private theorem adjacentMono (a : ℕ → ℝ) {d : ℕ}
    (step : ∀ i < d, a i < a (i + 1)) {i j : ℕ} (ij : i ≤ j) (jd : j ≤ d) :
    a i ≤ a j := by
  induction j with
  | zero => simp [Nat.eq_zero_of_le_zero ij]
  | succ j ih =>
    by_cases eq : i = j + 1
    · rw [eq]
    · exact (ih (by omega) (by omega)).trans (step j (by omega)).le

set_option maxHeartbeats 700000 in
/-- Every adjacent pair of checked dyadic nodes contains a distinct negative root. -/
theorem negativeMeshOK_sound {cs : List ℤ} {nodes : Array LongCycleFinite.Dyadic}
    (h : negativeMeshOK cs nodes = true) :
    Nonempty (QuotientMeshRoots (ofCoeffs cs) nodes (nodes.size - 1)) := by
  obtain ⟨⟨⟨length, atZero⟩, values⟩, order⟩ :
      ((nodes.size = cs.length ∧ K3.naturalSign false cs LongCycleFinite.Dyadic.zero = true) ∧
        (List.range nodes.size).all (fun i ↦ (meshNode nodes i).less LongCycleFinite.Dyadic.zero &&
          K3.naturalSign (meshNegative (nodes.size - 1) i) cs (meshNode nodes i)) = true) ∧
        (List.range (nodes.size - 1)).all
          (fun i ↦ (meshNode nodes i).less (meshNode nodes (i + 1))) = true := by
    simpa only [negativeMeshOK, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  let a (i : ℕ) := (meshNode nodes i).value
  have hz : 0 < (ofCoeffs cs).eval 0 := by
    simpa only [Bool.false_eq_true, if_false, LongCycleFinite.Dyadic.value_zero] using K3.naturalSign_sound atZero
  have data (i : ℕ) (hi : i < nodes.size) :
      a i < 0 ∧ HasSign (meshNegative (nodes.size - 1) i) ((ofCoeffs cs).eval (a i)) := by
    obtain ⟨neg, sign⟩ := Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp values i (List.mem_range.mpr hi))
    exact ⟨by simpa only [LongCycleFinite.Dyadic.value_zero] using (LongCycleFinite.Dyadic.less_iff _ _).mp neg,
      K3.naturalSign_sound sign⟩
  have step (i : ℕ) (hi : i < nodes.size - 1) : a i < a (i + 1) :=
    (LongCycleFinite.Dyadic.less_iff _ _).mp (List.all_eq_true.mp order i (List.mem_range.mpr hi))
  have crossing (i : Fin (nodes.size - 1)) :
      (ofCoeffs cs).eval (a i.val) * (ofCoeffs cs).eval (a (i.val + 1)) < 0 := by
    have hi := i.isLt
    have next := (data (i.val + 1) (by omega)).2
    rw [meshNegative_next hi] at next
    exact oppositeSigns (data i.val (by omega)).2 next
  have bracket (i : Fin (nodes.size - 1)) :
      ∃ x, a i.val < x ∧ x < a (i.val + 1) ∧ (ofCoeffs cs).eval x = 0 :=
    root_between (ofCoeffs cs) (step i.val i.isLt) (crossing i)
  choose roots located using bracket
  have sorted : StrictMono roots := by
    intro i j ij
    have middle : a (i.val + 1) ≤ a j.val := adjacentMono a step (by exact ij) (by omega)
    exact (located i).2.1.trans_le (middle.trans (located j).1.le)
  have bound : (ofCoeffs cs).natDegree ≤ nodes.size - 1 :=
    (ofCoeffs_degree_le cs).trans_eq (congrArg (· - 1) length.symm)
  have nonzero : ofCoeffs cs ≠ 0 := by intro z; simp [z] at hz
  exact ⟨⟨roots, hz, bound, sorted, fun i ↦ (located i).2.1.trans
      (data (i.val+1) (by have hi := i.isLt; omega)).1,
    fun i ↦ (located i).2.2, fun i ↦ ⟨(located i).1, (located i).2.1⟩,
    factor_of_degree_bound roots nonzero bound sorted.injective (fun i ↦ (located i).2.2)⟩⟩

/-- Exact complete root count of the original row after reinserting its zero root. -/
theorem QuotientMeshRoots.full_root_count {p : ℝ[X]} {nodes : Array LongCycleFinite.Dyadic} {d : ℕ}
    (m : QuotientMeshRoots p nodes d) :
    (X * p).Splits ∧ (X * p).roots.Nodup ∧ 0 ∈ (X * p).roots ∧
      (X * p).roots.card = d + 1 ∧ ((X * p).roots.filter (· < 0)).card = d := by
  classical
  let negative := (univ : Finset (Fin d)).map (⟨m.point, m.ordered.injective⟩ : Fin d ↪ ℝ)
  have negative_count : negative.card = d := by simp [negative]
  have negative_sign {x : ℝ} (h : x ∈ negative) : x < 0 := by
    obtain ⟨i, _, rfl⟩ := mem_map.mp h
    exact m.negative i
  have zero_notMem : (0 : ℝ) ∉ negative := fun h ↦ (lt_irrefl 0) (negative_sign h)
  let all := insert (0 : ℝ) negative
  have all_count : all.card = d + 1 := by
    dsimp [all]
    rw [card_insert_of_notMem zero_notMem, negative_count]
  have nonzero : p ≠ 0 := by
    intro z
    have hz := m.positiveAtZero
    simp [z] at hz
  have upper : (X * p).natDegree ≤ d + 1 := by
    apply natDegree_mul_le.trans
    rw [natDegree_X]
    have h := m.degreeBound
    omega
  have exactly : (X * p).roots = all.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      rcases mem_insert.mp hx with eq | neg
      · subst x
        simp
      · obtain ⟨i, _, rfl⟩ := mem_map.mp neg
        simp [m.roots i]
    · rw [all_count]
      exact upper
    · exact mul_ne_zero X_ne_zero nonzero
  have total : (X * p).roots.card = d + 1 := exactly ▸ all_count
  have split : (X * p).Splits := splits_iff_card_roots.mpr
    (total.trans (le_antisymm upper (total ▸ (X * p).card_roots')).symm)
  refine ⟨split, exactly ▸ all.nodup, ?_, total, ?_⟩
  · rw [exactly]
    change (0 : ℝ) ∈ all
    exact mem_insert_self _ _
  · rw [exactly]
    change (all.filter (· < 0)).card = d
    have kept : all.filter (· < 0) = negative := by
      ext x
      simp only [mem_filter, all, mem_insert]
      exact ⟨fun ⟨h, neg⟩ ↦ h.resolve_left (fun eq ↦ (lt_irrefl (0 : ℝ)) (by simpa only [eq] using neg)),
        fun h ↦ ⟨Or.inr h, negative_sign h⟩⟩
    rw [kept, negative_count]

/-- From the checked coefficient list through the sign mesh to the complete original roots. -/
theorem original_root_count_of_checks {n k : ℕ} (hn : 0 < n)
    {cs : List ℤ} {nodes : Array LongCycleFinite.Dyadic}
    (coefficients : descentRowDP n k = (0 :: cs) ++ [0])
    (mesh : negativeMeshOK cs nodes = true) :
    let p := (DescentTwoLetters.row n k).map (Int.castRingHom ℝ)
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧
      p.roots.card = nodes.size - 1 + 1 ∧
      (p.roots.filter (· < 0)).card = nodes.size - 1 := by
  dsimp only
  rw [row_eq_of_checkedCoeffs hn coefficients]
  obtain ⟨m⟩ := negativeMeshOK_sound mesh
  exact m.full_root_count

#print axioms ofCoeffs_descentRowDP
#print axioms negativeMeshOK_sound
#print axioms QuotientMeshRoots.full_root_count
#print axioms original_root_count_of_checks

end
end LongCycleBounds.DescentNecklace
