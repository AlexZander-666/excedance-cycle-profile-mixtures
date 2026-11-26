import LongCycleBounds.CycleProfileCounterexample
import LongCycleBounds.DescentFiniteRoots

/-! Complementary short-cycle supports whose two original rows lose real-rootedness
under the equal-weight average. -/

namespace LongCycleBounds.CycleProfile.Mixed44

open Polynomial LongCycleFinite
open LongCycleBounds.DescentNecklace (negativeMeshOK negativeMeshOK_sound)
open Counterexample (coefficients coefficients_correct jet jet_correct laguerre laguerre_nonneg_of_splits)

def allowedA : List ℕ :=
  [2, 4, 6, 9, 11, 13, 16, 18, 20, 23, 25, 27, 30, 32, 34, 36, 37, 39, 41, 43]

def allowedB : List ℕ :=
  [3, 5, 7, 8, 10, 12, 14, 15, 17, 19, 21, 22, 24, 26, 28, 29, 31, 33, 35, 38, 40, 42]

/-- The same unit tail is present in both endpoint profiles. -/
def profile (short : List ℕ) (j : ℕ) : ℤ := if 44 ≤ j ∨ j ∈ short then 1 else 0

def weights (short : List ℕ) (j : ℕ) : ℝ := (profile short j : ℝ)

theorem profiles_admissible (short : List ℕ) (h : short = allowedA ∨ short = allowedB) :
    weights short 1 = 0 ∧ (∀ j, weights short j = 0 ∨ weights short j = 1) ∧
      ∀ j ≥ 44, weights short j = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rcases h with rfl | rfl <;> norm_num [weights, profile, allowedA, allowedB]
  · intro j
    unfold weights profile
    split <;> simp
  · intro j hj
    simp [weights, profile, hj]

/-- Below the common tail each nontrivial cycle length belongs to precisely one profile. -/
theorem complementary : ∀ j : Fin 44, 2 ≤ j.val →
    profile allowedB j.val = 1 - profile allowedA j.val := by decide +kernel

def coeffA : List ℤ :=
  [1, 8796093022164, 338301004440220823666,
   82707496019228574672959879, 1250585935546571885881953699352, 3300692527109093457280989513790508,
   2562995687529342675882028451652208174, 772872960530677267195784320940549669058, 109896221108481231876579815296288258062708,
   8400080743080299418130488579019940234085722, 378272183431699502107118509963562427061977442, 10720714617384643462820414819459114208739458086,
   200754185453002722612070463361192729218419742842, 2576262524258928492043522855621155154239974642383, 23298368875831126219422323912767218358903660612566,
   151719467219469700697648402132675145734758709021354, 723410454618506209027031093908902853762210618816341, 2557987898397338135308638982471893788572058251711494,
   6772004762220998447520114332630983902577810782225285, 13514425929650452710341594720719070736144386867702730, 20422255787682636608617316847893410226260627425773010,
   23428902080872825587558800313123533809727837873206095, 20422255787682636608617316847893410226260627425773010, 13514425929650452710341594720719070736144386867702730,
   6772004762220998447520114332630983902577810782225285, 2557987898397338135308638982471893788572058251711494, 723410454618506209027031093908902853762210618816341,
   151719467219469700697648402132675145734758709021354, 23298368875831126219422323912767218358903660612566, 2576262524258928492043522855621155154239974642383,
   200754185453002722612070463361192729218419742842, 10720714617384643462820414819459114208739458086, 378272183431699502107118509963562427061977442,
   8400080743080299418130488579019940234085722, 109896221108481231876579815296288258062708, 772872960530677267195784320940549669058,
   2562995687529342675882028451652208174, 3300692527109093457280989513790508, 1250585935546571885881953699352,
   82707496019228574672959879, 338301004440220823666, 8796093022164,
   1]

def nodesA : Array LongCycleFinite.Dyadic :=
  #[⟨-13194081842438, 0⟩, ⟨-4398046388104, 0⟩, ⟨-19222273, 0⟩, ⟨-121423, 0⟩,
    ⟨-7470, 0⟩, ⟨-1324, 0⟩, ⟨-401, 0⟩, ⟨-153, 0⟩,
    ⟨-73, 0⟩, ⟨-40, 0⟩, ⟨-24, 0⟩, ⟨-16, 0⟩,
    ⟨-11, 0⟩, ⟨-7, 0⟩, ⟨-5, 0⟩, ⟨-4, 0⟩,
    ⟨-3, 0⟩, ⟨-5, 1⟩, ⟨-17, 3⟩, ⟨-3, 1⟩,
    ⟨-5, 2⟩, ⟨-1, 0⟩, ⟨-3, 2⟩, ⟨-1, 1⟩,
    ⟨-7, 4⟩, ⟨-3, 3⟩, ⟨-9, 5⟩, ⟨-7, 5⟩,
    ⟨-5, 5⟩, ⟨-1, 3⟩, ⟨-5, 6⟩, ⟨-1, 4⟩,
    ⟨-5, 7⟩, ⟨-3, 7⟩, ⟨-3, 8⟩, ⟨-3, 9⟩,
    ⟨-1, 9⟩, ⟨-1, 10⟩, ⟨-1, 12⟩, ⟨-1, 15⟩,
    ⟨-1, 19⟩, ⟨-1, 27⟩, ⟨-3, 45⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem tableA : coefficients (profile allowedA) 44 = 0 :: coeffA := by
  decide +kernel

private theorem signsA : negativeMeshOK coeffA nodesA = true := by
  decide +kernel

def coeffB : List ℤ :=
  [1, 10078054121080, 428163170741129215387,
   105730808892246488125302760, 1696776891066870633188552677885, 4631814058035834126144659199936028,
   3480368000198935423729439265772264629, 1039525066108167209159426718897926731200, 148014994203490001258750639468792862141559,
   11352056247263060594366398138453160680209704, 511586587978730589447320831105796168103665605, 14439365058258119582834179968654053943012083240,
   267860576807681547316477996292847412654320821332, 3389874840778781331513402487482157452672981930096, 30130641601527480203730972557297486756309783763940,
   192451551931775558296711171391071724275488539073528, 899428115960666948362914643158998006389388943242442, 3119692810012908261242429720122021566487323148016736,
   8119583170815941102516175349041367507766674699529438, 15988230656731226523405052398873910430537094187876408, 23954594135992099979349605763679162774154920134352278,
   27400450617675295538213090516160648310508089891037928, 23954594135992099979349605763679162774154920134352278, 15988230656731226523405052398873910430537094187876408,
   8119583170815941102516175349041367507766674699529438, 3119692810012908261242429720122021566487323148016736, 899428115960666948362914643158998006389388943242442,
   192451551931775558296711171391071724275488539073528, 30130641601527480203730972557297486756309783763940, 3389874840778781331513402487482157452672981930096,
   267860576807681547316477996292847412654320821332, 14439365058258119582834179968654053943012083240, 511586587978730589447320831105796168103665605,
   11352056247263060594366398138453160680209704, 148014994203490001258750639468792862141559, 1039525066108167209159426718897926731200,
   3480368000198935423729439265772264629, 4631814058035834126144659199936028, 1696776891066870633188552677885,
   105730808892246488125302760, 428163170741129215387, 10078054121080,
   1]

def nodesB : Array LongCycleFinite.Dyadic :=
  #[⟨-15117017454293, 0⟩, ⟨-5039026936391, 0⟩, ⟨-21233925, 0⟩, ⟨-122542, 0⟩,
    ⟨-8028, 0⟩, ⟨-1371, 0⟩, ⟨-362, 0⟩, ⟨-158, 0⟩,
    ⟨-75, 0⟩, ⟨-41, 0⟩, ⟨-25, 0⟩, ⟨-16, 0⟩,
    ⟨-10, 0⟩, ⟨-7, 0⟩, ⟨-5, 0⟩, ⟨-4, 0⟩,
    ⟨-3, 0⟩, ⟨-9, 2⟩, ⟨-15, 3⟩, ⟨-3, 1⟩,
    ⟨-5, 2⟩, ⟨-1, 0⟩, ⟨-3, 2⟩, ⟨-5, 3⟩,
    ⟨-1, 1⟩, ⟨-3, 3⟩, ⟨-5, 4⟩, ⟨-7, 5⟩,
    ⟨-5, 5⟩, ⟨-1, 3⟩, ⟨-3, 5⟩, ⟨-1, 4⟩,
    ⟨-5, 7⟩, ⟨-3, 7⟩, ⟨-3, 8⟩, ⟨-3, 9⟩,
    ⟨-3, 10⟩, ⟨-1, 10⟩, ⟨-1, 12⟩, ⟨-1, 15⟩,
    ⟨-1, 19⟩, ⟨-1, 27⟩, ⟨-1, 44⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem tableB : coefficients (profile allowedB) 44 = 0 :: coeffB := by
  decide +kernel

private theorem signsB : negativeMeshOK coeffB nodesB = true := by
  decide +kernel

private theorem identify {short : List ℕ} {cs : List ℤ}
    (h : coefficients (profile short) 44 = 0 :: cs) :
    row 44 (weights short) = X * ofCoeffs cs := by
  have eq := coefficients_correct (profile short) 44
  rw [h] at eq
  change row 44 (fun j => (profile short j : ℝ)) = X * ofCoeffs cs
  simpa only [ofCoeffs, Int.cast_zero, C_0, zero_add] using eq.symm

/-- Every original endpoint has 42 distinct negative zeros and one simple zero. -/
theorem endpoints (short : List ℕ) (h : short = allowedA ∨ short = allowedB) :
    let p := row 44 (weights short)
    p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.roots.card = 43 ∧
      (p.roots.filter (· < 0)).card = 42 := by
  rcases h with rfl | rfl
  · obtain ⟨cert⟩ := negativeMeshOK_sound signsA
    have sz : nodesA.size - 1 = 42 := by decide
    simpa only [identify tableA, sz] using cert.full_root_count
  · obtain ⟨cert⟩ := negativeMeshOK_sound signsB
    have sz : nodesB.size - 1 = 42 := by decide
    simpa only [identify tableB, sz] using cert.full_root_count


noncomputable def sumRows (p q : ℝ[X]) : ℝ[X] := p + q

noncomputable abbrev mixture := sumRows (row 44 (weights allowedA)) (row 44 (weights allowedB))
def mixedCoeffs := addCoeffs (0 :: coeffA) (0 :: coeffB)

private theorem polynomial_table {short : List ℕ} {cs : List ℤ}
    (e : coefficients (profile short) 44 = cs) : ofCoeffs cs = row 44 (weights short) := by
  rw [← e]
  exact coefficients_correct (profile short) 44

private theorem mix_map (a b : List ℤ) (p q : ℝ[X]) (ha : ofCoeffs a = p)
    (hb : ofCoeffs b = q) : ofCoeffs (addCoeffs a b) = sumRows p q := by
  rw [ofCoeffs_addCoeffs, ha, hb, sumRows]

private theorem mixed_representation : ofCoeffs mixedCoeffs = mixture :=
  mix_map (0 :: coeffA) (0 :: coeffB) (row 44 (weights allowedA)) (row 44 (weights allowedB))
    (polynomial_table (short := allowedA) (cs := 0 :: coeffA) tableA)
    (polynomial_table (short := allowedB) (cs := 0 :: coeffB) tableB)

def exactGap : ℚ :=
  -6173892803981545145020946953861000138562340606290354938327449110608313449506311357186071746898428032025 /
  4835703278458516698824704

private theorem rational_gap :
    let J := jet (-1/2) mixedCoeffs
    J.first ^ 2 - J.value * J.second = exactGap := by decide +kernel

theorem mixture_gap : laguerre mixture ((-1/2 : ℚ) : ℝ) = (exactGap : ℝ) := by
  have g := rational_gap
  obtain ⟨v, d, dd⟩ := jet_correct (-1/2) mixedCoeffs
  rw [← mixed_representation]
  unfold Counterexample.laguerre
  rw [← v, ← d, ← dd]
  exact_mod_cast g

theorem mixture_not_splits : ¬mixture.Splits := by
  intro h
  have lower := laguerre_nonneg_of_splits h ((-1/2 : ℚ) : ℝ)
  rw [mixture_gap] at lower
  exact (not_le_of_gt (show (exactGap : ℝ) < 0 by
    exact_mod_cast (show exactGap < 0 by norm_num [exactGap]))) lower

noncomputable def average (a b : ℝ[X]) : ℝ[X] := C (1/2 : ℝ) * a + C (1/2 : ℝ) * b

private theorem double_average (a b : ℝ[X]) : sumRows a b = C (2 : ℝ) * average a b := by
  unfold sumRows average
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← C_mul]
  norm_num

private theorem average_of_sum (a b : ℝ[X]) (h : ¬(sumRows a b).Splits) : ¬(average a b).Splits := by
  intro hs
  apply h
  rw [double_average a b]
  exact (Splits.C _).mul hs

theorem convex_not_splits :
    ¬(average (row 44 (weights allowedA)) (row 44 (weights allowedB))).Splits :=
  average_of_sum (row 44 (weights allowedA)) (row 44 (weights allowedB)) mixture_not_splits

end LongCycleBounds.CycleProfile.Mixed44
