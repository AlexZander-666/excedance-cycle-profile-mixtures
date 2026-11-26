import LongCycleBounds.CycleProfileCounterexample
import LongCycleBounds.DescentFiniteRoots

/-! A fixed-size mixture of two real-rooted, independently weighted excedance rows. -/

namespace LongCycleBounds.CycleProfile.Mixed34
open Polynomial LongCycleFinite
open LongCycleBounds.DescentNecklace (negativeMeshOK negativeMeshOK_sound)
open Counterexample (coefficients coefficients_correct jet jet_correct laguerre laguerre_nonneg_of_splits)

def allowedA : List ℕ := [3, 4, 7, 10, 13, 14, 16, 17, 20, 23]
def allowedB : List ℕ := [2, 3, 5, 6, 8, 9, 12, 15, 18, 21, 24, 27]

/-- The same unit tail is present in both endpoint profiles. -/
def profile (short : List ℕ) (j : ℕ) : ℤ := if 34 ≤ j ∨ j ∈ short then 1 else 0

def weights (short : List ℕ) (j : ℕ) : ℝ := (profile short j : ℝ)

theorem profiles_admissible (short : List ℕ) (h : short = allowedA ∨ short = allowedB) :
    weights short 1 = 0 ∧ (∀ j, weights short j = 0 ∨ weights short j = 1) ∧
      ∀ j ≥ 34, weights short j = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rcases h with rfl | rfl <;> norm_num [weights, profile, allowedA, allowedB]
  · intro j
    unfold weights profile
    split <;> simp
  · intro j hj
    simp [weights, profile, hj]

def coeffA : List ℤ :=
  [1, 11148713308, 6752455134458536,
  95437016699527064720, 158346956724514766364800, 63509232104525222773287104,
  9299139174465552395312950572, 617903009386726823890164983964, 21350705734536290876178810774420,
  420962140723799690514022152686020, 5060024089831075082493005434854860, 38947176274432302511285147642609440,
  198913065502564996563394813993856160, 691358470138707573100254955796135120, 1664256089581800625971449588386829920,
  2806917422295179879364552561016522500, 3338794502952139980203755858129897110, 2806917422295179879364552561016522500,
  1664256089581800625971449588386829920, 691358470138707573100254955796135120, 198913065502564996563394813993856160,
  38947176274432302511285147642609440, 5060024089831075082493005434854860, 420962140723799690514022152686020,
  21350705734536290876178810774420, 617903009386726823890164983964, 9299139174465552395312950572,
  63509232104525222773287104, 158346956724514766364800, 95437016699527064720,
  6752455134458536, 11148713308, 1]

def nodesA : Array LongCycleFinite.Dyadic :=
  #[⟨-16722161406, 0⟩, ⟨-5574349434, 0⟩, ⟨-301928, 0⟩, ⟨-6966, 0⟩,
    ⟨-814, 0⟩, ⟨-195, 0⟩, ⟨-75, 0⟩, ⟨-35, 0⟩,
    ⟨-19, 0⟩, ⟨-11, 0⟩, ⟨-6, 0⟩, ⟨-4, 0⟩,
    ⟨-3, 0⟩, ⟨-5, 1⟩, ⟨-7, 2⟩, ⟨-5, 2⟩,
    ⟨-1, 0⟩, ⟨-3, 2⟩, ⟨-1, 1⟩, ⟨-3, 3⟩,
    ⟨-9, 5⟩, ⟨-3, 4⟩, ⟨-9, 6⟩, ⟨-3, 5⟩,
    ⟨-3, 6⟩, ⟨-1, 5⟩, ⟨-3, 8⟩, ⟨-1, 8⟩,
    ⟨-1, 9⟩, ⟨-1, 12⟩, ⟨-1, 15⟩, ⟨-1, 21⟩,
    ⟨-1, 34⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem tableA : coefficients (profile allowedA) 34 = 0 :: coeffA := by
  decide +kernel

private theorem signsA : negativeMeshOK coeffA nodesA = true := by
  decide +kernel

def coeffB : List ℤ :=
  [1, 8589934558, 5574167851565002,
  78010515511569612338, 127736040370878602373365, 51614372832779267430235022,
  7668643303665641421175375506, 522453459388808877324936643326, 18715204746463487266279410941748,
  386505111331796383009312726804578, 4899676923981633872846168005340088, 39780384784236483812876807217185850,
  213017634203332713602999750503507743, 768832655793217599017835860447627898, 1901056442377025586768048292099049268,
  3257655811526566964113527823595085198, 3895337193490883453629122983773709535, 3257655811526566964113527823595085198,
  1901056442377025586768048292099049268, 768832655793217599017835860447627898, 213017634203332713602999750503507743,
  39780384784236483812876807217185850, 4899676923981633872846168005340088, 386505111331796383009312726804578,
  18715204746463487266279410941748, 522453459388808877324936643326, 7668643303665641421175375506,
  51614372832779267430235022, 127736040370878602373365, 78010515511569612338,
  5574167851565002, 8589934558, 1]

def nodesB : Array LongCycleFinite.Dyadic :=
  #[⟨-12883928387, 0⟩, ⟨-4294960142, 0⟩, ⟨-323573, 0⟩, ⟨-6880, 0⟩,
    ⟨-799, 0⟩, ⟨-197, 0⟩, ⟨-75, 0⟩, ⟨-35, 0⟩,
    ⟨-19, 0⟩, ⟨-11, 0⟩, ⟨-8, 0⟩, ⟨-6, 0⟩,
    ⟨-3, 0⟩, ⟨-5, 1⟩, ⟨-7, 2⟩, ⟨-5, 2⟩,
    ⟨-1, 0⟩, ⟨-3, 2⟩, ⟨-1, 1⟩, ⟨-3, 3⟩,
    ⟨-1, 2⟩, ⟨-5, 5⟩, ⟨-15, 7⟩, ⟨-5, 6⟩,
    ⟨-3, 6⟩, ⟨-1, 5⟩, ⟨-3, 8⟩, ⟨-1, 8⟩,
    ⟨-1, 9⟩, ⟨-1, 12⟩, ⟨-1, 15⟩, ⟨-1, 21⟩,
    ⟨-3, 35⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem tableB : coefficients (profile allowedB) 34 = 0 :: coeffB := by
  decide +kernel

private theorem signsB : negativeMeshOK coeffB nodesB = true := by
  decide +kernel

private theorem identify {short : List ℕ} {cs : List ℤ}
    (h : coefficients (profile short) 34 = 0 :: cs) :
    row 34 (weights short) = X * ofCoeffs cs := by
  have eq := coefficients_correct (profile short) 34
  rw [h] at eq
  change row 34 (fun j => (profile short j : ℝ)) = X * ofCoeffs cs
  simpa only [ofCoeffs, Int.cast_zero, C_0, zero_add] using eq.symm

/-- Every original endpoint has 32 distinct negative zeros and one simple zero. -/
theorem endpoints (short : List ℕ) (h : short = allowedA ∨ short = allowedB) :
    let p := row 34 (weights short)
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.roots.card = 33 ∧
      (p.roots.filter (· < 0)).card = 32 := by
  rcases h with rfl | rfl
  · obtain ⟨cert⟩ := negativeMeshOK_sound signsA
    have sz : nodesA.size - 1 = 32 := by decide
    simpa only [identify tableA, sz] using cert.full_root_count
  · obtain ⟨cert⟩ := negativeMeshOK_sound signsB
    have sz : nodesB.size - 1 = 32 := by decide
    simpa only [identify tableB, sz] using cert.full_root_count


noncomputable def oneTwo (p q : ℝ[X]) : ℝ[X] := p + C (2 : ℝ) * q

noncomputable abbrev mixture : ℝ[X] := oneTwo (row 34 (weights allowedA)) (row 34 (weights allowedB))

def mixedCoeffs := addCoeffs (0 :: coeffA) (scaleCoeffs 2 (0 :: coeffB))

private theorem polynomial_table {short : List ℕ} {cs : List ℤ}
    (e : coefficients (profile short) 34 = cs) : ofCoeffs cs = row 34 (weights short) := by
  rw [← e]
  exact coefficients_correct (profile short) 34

private theorem mix_map (a b : List ℤ) (p q : ℝ[X]) (ha : ofCoeffs a = p)
    (hb : ofCoeffs b = q) : ofCoeffs (addCoeffs a (scaleCoeffs 2 b)) = oneTwo p q := by
  rw [ofCoeffs_addCoeffs, ofCoeffs_scaleCoeffs, ha, hb]
  norm_num [oneTwo]

private theorem mixed_representation : ofCoeffs mixedCoeffs = mixture :=
  mix_map (0 :: coeffA) (0 :: coeffB) (row 34 (weights allowedA)) (row 34 (weights allowedB))
    (polynomial_table (short := allowedA) (cs := 0 :: coeffA) tableA)
    (polynomial_table (short := allowedB) (cs := 0 :: coeffB) tableB)

def exactGap : ℚ :=
  -8727587047550814985408940117838389400548646519066086843479435356337931155075329074624014093474783028525789068085429 /
  68940878844249415387681874250211215560124600187918986193835735321044921875

private theorem rational_gap :
    let J := jet (-2/15) mixedCoeffs
    J.first ^ 2 - J.value * J.second = exactGap := by decide +kernel

theorem mixture_gap : laguerre mixture ((-2/15 : ℚ) : ℝ) = (exactGap : ℝ) := by
  have g := rational_gap
  obtain ⟨v, d, dd⟩ := jet_correct (-2/15) mixedCoeffs
  rw [← mixed_representation]
  unfold Counterexample.laguerre
  rw [← v, ← d, ← dd]
  exact_mod_cast g

theorem mixture_not_splits : ¬mixture.Splits := by
  intro h
  have lower := laguerre_nonneg_of_splits h ((-2/15 : ℚ) : ℝ)
  rw [mixture_gap] at lower
  exact (not_le_of_gt (show (exactGap : ℝ) < 0 by
    exact_mod_cast (show exactGap < 0 by norm_num [exactGap]))) lower

private theorem normalize_mixture (a b : ℝ[X]) :
    a + C (2 : ℝ) * b = C (3 : ℝ) * (C (1/3 : ℝ) * a + C (2/3 : ℝ) * b) := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
  norm_num

noncomputable def convexThirds (a b : ℝ[X]) : ℝ[X] := C (1/3 : ℝ) * a + C (2/3 : ℝ) * b

private theorem convex_of_not_splits (a b : ℝ[X]) (h : ¬(oneTwo a b).Splits) :
    ¬(convexThirds a b).Splits := by
  intro h'
  apply h
  unfold oneTwo
  rw [normalize_mixture a b]
  exact (Splits.C _).mul h'

/-- The genuine fixed-size convex combination with weights one third and two thirds. -/
theorem convex_not_splits :
    ¬(convexThirds (row 34 (weights allowedA)) (row 34 (weights allowedB))).Splits :=
  convex_of_not_splits (row 34 (weights allowedA)) (row 34 (weights allowedB)) mixture_not_splits

end LongCycleBounds.CycleProfile.Mixed34
