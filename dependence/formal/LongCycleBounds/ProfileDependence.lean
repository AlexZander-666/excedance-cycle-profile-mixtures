import LongCycleBounds.LocalProfile34
import LongCycleBounds.LocalProfile44
import LongCycleBounds.LowerProfile39

namespace LongCycleBounds.CycleProfile
open Polynomial Equiv

/-- Expanding the product separates the two choices for every individual cycle of the permutation. -/
theorem independent_cycle_assignments {n : ℕ} (σ : Perm (Fin n)) (a b : ℕ → ℝ) (l r : ℝ) :
    cycleWeight (fun j => l * a j + r * b j) σ =
      ∑ choices ∈ σ.cycleFactorsFinset.powerset,
        (∏ cycle ∈ choices, l * a cycle.support.card) *
        ∏ cycle ∈ σ.cycleFactorsFinset \ choices, r * b cycle.support.card := by
  classical
  rw [cycleWeight, Perm.cycleType_def, Multiset.map_map]
  exact Finset.prod_add _ _ _

/-- The fixed-size comparison with identical one-cycle acceptance probabilities. -/
def DependenceContrast (n : ℕ) (a b : ℕ → ℝ) (l r : ℝ) : Prop :=
  ConvexProfileWitness n a b l r ∧
    SimpleEndpointRow n (row n (fun j => l * a j + r * b j))

theorem uniform44 {j : ℕ} (lo : 2 ≤ j) (hi : j < 44) : Local44.marginal j = 1/2 := by
  have eq := Mixed44.complementary ⟨j,hi⟩ lo
  change Mixed44.profile Mixed44.allowedB j = 1 - Mixed44.profile Mixed44.allowedA j at eq
  simp only [Local44.marginal, Mixed44.weights, eq, Int.cast_sub, Int.cast_one]
  ring

/-- Circle choices sharing their one-cycle probabilities can have different root behavior.
The additional size-39 to size-40 transition belongs to one deterministic legal profile. -/
theorem joint_comparison :
    DependenceContrast 34 (Mixed34.weights Mixed34.allowedA) (Mixed34.weights Mixed34.allowedB)
      (1/3) (2/3) ∧
    DependenceContrast 44 (Mixed44.weights Mixed44.allowedA) (Mixed44.weights Mixed44.allowedB)
      (1/2) (1/2) ∧
    LegalBinaryProfile 39 Counterexample.weight ∧
    SimpleEndpointRow 39 (row 39 Counterexample.weight) ∧
    ¬ (row 40 Counterexample.weight).Splits := by
  exact ⟨⟨two_convex_failures.1, Local34.independent_simple⟩,
    ⟨two_convex_failures.2, Local44.independent_simple⟩,
    ⟨Counterexample.weight_one, Counterexample.binary_weights, Counterexample.tail⟩,
    Lower39.simple, Counterexample.not_splits⟩

end LongCycleBounds.CycleProfile
