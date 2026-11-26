import LongCycles.Statement

/-! One- and two-letter specializations of the ordinary descents of allowed permutations. -/

noncomputable section
namespace LongCycleBounds.DescentTwoLetters
open Finset Polynomial LongCycles
open scoped Classical

/-- The original ordinary descent polynomial on permutations whose cycle lengths are at least k. -/
def row (n k : ℕ) : Polynomial ℤ := by
  classical
  exact ∑ σ : Equiv.Perm (Fin n), if Allowed k σ then X ^ descents σ else 0

/-- The adjacent descent positions can be indexed without including the last letter. -/
theorem descents_eq_card {m : ℕ} (σ : Equiv.Perm (Fin (m+1))) :
    descents σ = (univ.filter fun i : Fin m ↦ σ i.succ < σ i.castSucc).card := by
  classical
  unfold descents
  rw [← Finset.card_map (Fin.castSuccEmb : Fin m ↪ Fin (m+1))]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_map, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨y, hy, lt⟩
    have hxm : x.val < m := by omega
    let i : Fin m := ⟨x.val,hxm⟩
    have xi : i.castSucc = x := Fin.ext rfl
    have yi : i.succ = y := Fin.ext hy.symm
    exact ⟨i, xi ▸ yi ▸ lt, xi⟩
  · rintro ⟨i, lt, rfl⟩
    exact ⟨i.succ,rfl,lt⟩

theorem descents_zero_iff {m : ℕ} (σ : Equiv.Perm (Fin (m+1))) :
    descents σ = 0 ↔ σ = 1 := by
  classical
  rw [descents_eq_card, card_filter_eq_zero_iff]
  simp only [mem_univ, true_implies, not_lt]
  constructor
  · intro h
    have mono : StrictMono σ := Fin.strictMono_iff_lt_succ.mpr fun i ↦
      lt_of_le_of_ne (h i) (fun eq ↦ (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne (σ.injective eq))
    apply Equiv.ext
    intro i
    exact congrFun mono.eq_id i
  · rintro rfl i
    exact (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le

theorem descents_full_iff {m : ℕ} (σ : Equiv.Perm (Fin (m+1))) :
    descents σ = m ↔ σ = Fin.revPerm := by
  classical
  rw [descents_eq_card]
  conv_lhs => rhs; rw [← (show (univ : Finset (Fin m)).card = m by simp)]
  rw [card_filter_eq_iff]
  simp only [mem_univ, true_implies]
  constructor
  · intro h
    have anti : StrictAnti σ := Fin.strictAnti_iff_succ_lt.mpr h
    have eq := (Fin.rev_strictAnti.comp anti).eq_id
    apply Equiv.ext
    intro i
    have v := congrFun eq i
    simpa using congrArg Fin.rev v
  · rintro rfl i
    exact Fin.rev_strictAnti (show i.castSucc < i.succ from Fin.castSucc_lt_succ)

private theorem reversal_allowed {n : ℕ} (hn : 0<n) :
    Allowed 2 (Fin.revPerm : Equiv.Perm (Fin n)) ↔ Even n := by
  constructor
  · intro allow
    by_contra hnodd
    have odd : Odd n := Nat.not_even_iff_odd.mp hnodd
    obtain ⟨a,ha⟩ := odd
    let i : Fin n := ⟨a,by omega⟩
    have h := ne_fixed_of_allowed allow (by decide) i
    apply h
    apply Fin.ext
    change n - (a+1) = a
    omega
  · intro even i j hj hj2
    have ej : j=1 := by omega
    subst j
    rw [pow_one]
    intro bad
    have v := congrArg Fin.val bad
    change n - (i.val+1) = i.val at v
    obtain ⟨a,ha⟩ := even
    omega

private theorem reversal_not_allowed {m k : ℕ} (hk : 3 ≤ k) :
    ¬ Allowed k (Fin.revPerm : Equiv.Perm (Fin (m+1))) := by
  intro allow
  apply allow 0 2 (by decide) (by omega)
  simp [pow_two, Equiv.Perm.mul_apply]

/-- Coefficient of the descent row as an integer count on the original permutations. -/
theorem coeff_row (n k i : ℕ) :
    (row n k).coeff i =
      ∑ σ : Equiv.Perm (Fin n), if Allowed k σ ∧ descents σ = i then (1:ℤ) else 0 := by
  classical
  unfold row
  rw [Polynomial.finsetSum_coeff]
  apply sum_congr rfl
  intro σ _
  by_cases h : Allowed k σ
  · simp [h, Polynomial.coeff_X_pow, eq_comm]
  · simp [h]

/-- Fixed points exclude the unique weakly increasing word at cutoff at least two. -/
theorem constant_zero (m : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    (row (m+1) k).coeff 0 = 0 := by
  rw [coeff_row]
  apply sum_eq_zero
  intro σ _
  apply if_neg
  rintro ⟨allow, hd⟩
  obtain rfl := (descents_zero_iff σ).mp hd
  exact ne_fixed_of_allowed allow hk 0 rfl

/-- Only the reversing permutation can contribute the highest natural descent coefficient. -/
theorem top_coeff (m k : ℕ) : (row (m+1) k).coeff m =
    if Allowed k (Fin.revPerm : Equiv.Perm (Fin (m+1))) then 1 else 0 := by
  rw [coeff_row]
  classical
  trans ∑ σ : Equiv.Perm (Fin (m+1)), if σ = Fin.revPerm then
    (if Allowed k (Fin.revPerm : Equiv.Perm (Fin (m+1))) then (1:ℤ) else 0) else 0
  · apply sum_congr rfl
    intro σ _
    by_cases he : σ = Fin.revPerm <;> simp [descents_full_iff, he]
  · simp

theorem top_zero (m : ℕ) {k : ℕ} (hk : 3 ≤ k) : (row (m+1) k).coeff m = 0 := by
  rw [top_coeff, if_neg (reversal_not_allowed hk)]

theorem top_two (m : ℕ) : (row (m+1) 2).coeff m = if Even (m+1) then 1 else 0 := by
  rw [top_coeff, reversal_allowed (by omega)]
  split <;> simp_all

/-- The finite-alphabet binomial specialization of a descent coefficient list. -/
def letters (n q : ℕ) (d : ℕ → ℤ) : ℤ :=
  ∑ i ∈ range n, d i * ((q+n-1-i).choose n : ℤ)

private theorem letters_one_aux (m : ℕ) (d : ℕ → ℤ) :
    letters (m+1) 1 d = d 0 := by
  unfold letters
  rw [sum_range_succ']
  have z : (∑ i ∈ range m, d (i+1) * ((1+(m+1)-1-(i+1)).choose (m+1) : ℤ)) = 0 := by
    apply sum_eq_zero
    intro i _
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [z]
  simp

private theorem letters_two_aux (m : ℕ) (d : ℕ → ℤ) :
    letters (m+2) 2 d = ((m+3:ℕ):ℤ)*d 0+d 1 := by
  unfold letters
  rw [sum_range_succ', sum_range_succ']
  have z : (∑ i ∈ range m, d (i+1+1) *
      ((2+(m+2)-1-(i+1+1)).choose (m+2) : ℤ)) = 0 := by
    apply sum_eq_zero
    intro i _
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [z]
  rw [show 2+(m+2)-1= m+3 by omega]
  simp [Nat.choose_succ_self_right]
  ring

/-- Reverse a list at its natural endpoint n−1, including any zero endpoint coefficients. -/
def reverseList (n : ℕ) (d : ℕ → ℤ) (i : ℕ) : ℤ := d (n-1-i)

/-- The complementary minus ordinary finite-alphabet specialization. -/
def defect (n q : ℕ) (d : ℕ → ℤ) : ℤ := letters n q (reverseList n d) - letters n q d

theorem defect_one (m : ℕ) (d : ℕ → ℤ) : defect (m+2) 1 d = d (m+1)-d 0 := by
  unfold defect
  rw [letters_one_aux, letters_one_aux]
  rfl

/-- The extra top-minus-bottom term is kept so the cutoff-two correction is visible. -/
theorem defect_two (m : ℕ) (d : ℕ → ℤ) :
    defect (m+2) 2 d = ((m+3:ℕ):ℤ)*defect (m+2) 1 d + d m - d 1 := by
  rw [defect_one]
  unfold defect
  rw [letters_two_aux, letters_two_aux]
  unfold reverseList
  simp only [Nat.sub_zero, Nat.succ_sub_one]
  ring

/-- For k≥3, identity and reversal are excluded, leaving exactly one ascent minus one descent. -/
theorem row_extreme_difference (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    defect (m+2) 1 (row (m+2) k).coeff = 0 ∧
    defect (m+2) 2 (row (m+2) k).coeff =
      (row (m+2) k).coeff m - (row (m+2) k).coeff 1 := by
  have one : defect (m+2) 1 (row (m+2) k).coeff = 0 := by
    rw [defect_one, top_zero (m+1) hk, constant_zero (m+1) (by omega)]
    simp
  exact ⟨one, by rw [defect_two, one]; ring⟩

/-- At cutoff two the even-size reversal contributes an additional n+1 at alphabet size two. -/
theorem row_extreme_difference_two (m : ℕ) :
    defect (m+2) 1 (row (m+2) 2).coeff = (if Even (m+2) then 1 else 0) ∧
    defect (m+2) 2 (row (m+2) 2).coeff =
      (if Even (m+2) then ((m+3:ℕ):ℤ) else 0) +
        (row (m+2) 2).coeff m - (row (m+2) 2).coeff 1 := by
  have one : defect (m+2) 1 (row (m+2) 2).coeff = (if Even (m+2) then 1 else 0) := by
    rw [defect_one, top_two (m+1), constant_zero (m+1) (by decide), sub_zero]
  refine ⟨one, ?_⟩
  rw [defect_two, one]
  split <;> simp

#print axioms coeff_row
#print axioms descents_zero_iff
#print axioms descents_full_iff
#print axioms row_extreme_difference
#print axioms row_extreme_difference_two

end LongCycleBounds.DescentTwoLetters
