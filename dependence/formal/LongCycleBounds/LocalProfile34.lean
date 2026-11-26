import LongCycleBounds.ProfileRowScaling

/-! Independent cycle choices with the same single-cycle probabilities as the size-34 mixture. -/

namespace LongCycleBounds.CycleProfile.Local34
open Polynomial LongCycleFinite
open LongCycleBounds.DescentNecklace (negativeMeshOK negativeMeshOK_sound)
open Counterexample (coefficients coefficients_correct)
open Mixed34 (allowedA allowedB weights)

/-- Numerator of the independent probability at cycle length j after scaling by 3^j. -/
def lifted : ℕ → ℤ
  | 0 => 0
  | j+1 => 3^j * (Mixed34.profile allowedA (j+1) + 2 * Mixed34.profile allowedB (j+1))

noncomputable def marginal (j : ℕ) : ℝ :=
  (1/3) * weights allowedA j + (2/3) * weights allowedB j

theorem lift_eq (j : ℕ) : (lifted j : ℝ) = (3:ℝ)^j * marginal j := by
  cases j with
  | zero => norm_num [lifted, marginal, Mixed34.weights, Mixed34.profile, Mixed34.allowedA,
      Mixed34.allowedB]
  | succ j => simp only [lifted, marginal, Mixed34.weights, Int.cast_mul, Int.cast_add,
                Int.cast_pow, pow_succ]; push_cast; ring

def quotientCoeffs : List ℤ :=
  [16677181699666569, 160110386685066667927517424, 108238960196786567770350827669658,
  1533509867519847389867585379321036924, 2505543693022002130328426175364262542704, 1005806168369000343558458814061909552324464,
  147852435818589173829774647569585221447739194, 9929467073469880916684798295908279380132514556, 349037490723419283250874091728507568359864876682,
  7036408927303397689550743752120327251784108431052, 86713943130732445494916863538660842506663202271014, 683756816126135996036906516169139893846564949423848,
  3565560108678233544094939103410828556632445518769304, 12595517311067227455936279188240954240198094637122732, 30666929722792759088170496787504805188287881654886022,
  52068647714809174078228810913370408853246851690652104, 62070962231854547174982330602542796509868728445551818, 52068647714809174078228810913370408853246851690652104,
  30666929722792759088170496787504805188287881654886022, 12595517311067227455936279188240954240198094637122732, 3565560108678233544094939103410828556632445518769304,
  683756816126135996036906516169139893846564949423848, 86713943130732445494916863538660842506663202271014, 7036408927303397689550743752120327251784108431052,
  349037490723419283250874091728507568359864876682, 9929467073469880916684798295908279380132514556, 147852435818589173829774647569585221447739194,
  1005806168369000343558458814061909552324464, 2505543693022002130328426175364262542704, 1533509867519847389867585379321036924,
  108238960196786567770350827669658, 160110386685066667927517424, 16677181699666569]

def nodes : Array LongCycleFinite.Dyadic :=
  #[⟨-9663676416, 0⟩, ⟨-671744, 0⟩, ⟨-12800, 0⟩, ⟨-1312, 0⟩,
    ⟨-296, 0⟩, ⟨-104, 0⟩, ⟨-47, 0⟩, ⟨-25, 0⟩,
    ⟨-15, 0⟩, ⟨-9, 0⟩, ⟨-7, 0⟩, ⟨-5, 0⟩,
    ⟨-3, 0⟩, ⟨-5, 1⟩, ⟨-2, 0⟩, ⟨-3, 1⟩,
    ⟨-1, 0⟩, ⟨-3, 2⟩, ⟨-1, 1⟩, ⟨-3, 3⟩,
    ⟨-1, 2⟩, ⟨-3, 4⟩, ⟨-1, 3⟩, ⟨-3, 5⟩,
    ⟨-1, 4⟩, ⟨-1, 5⟩, ⟨-1, 6⟩, ⟨-1, 7⟩,
    ⟨-1, 9⟩, ⟨-1, 11⟩, ⟨-1, 14⟩, ⟨-1, 20⟩,
    ⟨-1, 34⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table : coefficients lifted 34 = 0 :: quotientCoeffs := by
  decide +kernel

private theorem signs : negativeMeshOK quotientCoeffs nodes = true := by
  decide +kernel

/-- Negative roots are all simple, and the original weighted row also has its simple zero. -/
theorem independent_simple : SimpleEndpointRow 34 (row 34 marginal) := by
  apply simple_unscale (c := (3:ℝ)^34) (by norm_num)
  rw [←row_rescale]
  have e := coefficients_correct lifted 34
  rw [table] at e
  have identify : row 34 (fun j => (3:ℝ)^j * marginal j) = X * ofCoeffs quotientCoeffs := by
    simpa only [ofCoeffs,Int.cast_zero,C_0,zero_add,lift_eq] using e.symm
  obtain ⟨cert⟩ := negativeMeshOK_sound signs
  have cnt : nodes.size - 1 = 32 := by decide
  simpa only [SimpleEndpointRow,identify,cnt] using cert.full_root_count
end LongCycleBounds.CycleProfile.Local34
