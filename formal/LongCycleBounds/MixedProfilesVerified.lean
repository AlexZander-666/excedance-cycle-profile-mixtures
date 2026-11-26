import LongCycleBounds.MixedProfile34
import LongCycleBounds.MixedProfile44

/-! Both certified failures of fixed-size convex compatibility, on the original permutations. -/

namespace LongCycleBounds.CycleProfile

open Polynomial

/-- A nonnegative binary length profile with no fixed points and an unrestricted upper tail. -/
def LegalBinaryProfile (k : ℕ) (w : ℕ → ℝ) : Prop :=
  w 1 = 0 ∧ (∀ j, w j = 0 ∨ w j = 1) ∧ ∀ j ≥ k, w j = 1

/-- The entire root multiset of an endpoint has cardinality n−1. -/
def SimpleEndpointRow (n : ℕ) (p : ℝ[X]) : Prop :=
  p.Splits ∧ p.roots.Nodup ∧ 0 ∈ p.roots ∧ p.roots.card = n-1 ∧
    (p.roots.filter (· < 0)).card = n-2

/-- A fixed-size convex non-splitting example with complete endpoint counts.
The two weights multiply the two whole permutation polynomials. -/
def ConvexProfileWitness (n : ℕ) (a b : ℕ → ℝ) (l r : ℝ) : Prop :=
  LegalBinaryProfile n a ∧ LegalBinaryProfile n b ∧ 0 < l ∧ 0 < r ∧ l+r=1 ∧
  SimpleEndpointRow n (row n a) ∧ SimpleEndpointRow n (row n b) ∧
  ¬(C l * row n a + C r * row n b).Splits

private theorem thirds_readout (p q : ℝ[X]) (h : ¬(Mixed34.convexThirds p q).Splits) :
    ¬(C (1/3 : ℝ) * p + C (2/3 : ℝ) * q).Splits := h

private theorem halves_readout (p q : ℝ[X]) (h : ¬(Mixed44.average p q).Splits) :
    ¬(C (1/2 : ℝ) * p + C (1/2 : ℝ) * q).Splits := h

/-- One-third and two-thirds at 34 letters, and equal halves at 44 letters. -/
theorem two_convex_failures :
    ConvexProfileWitness 34 (Mixed34.weights Mixed34.allowedA) (Mixed34.weights Mixed34.allowedB)
      (1/3) (2/3) ∧
    ConvexProfileWitness 44 (Mixed44.weights Mixed44.allowedA) (Mixed44.weights Mixed44.allowedB)
      (1/2) (1/2) := by
  constructor
  · exact ⟨Mixed34.profiles_admissible _ (Or.inl rfl),
      Mixed34.profiles_admissible _ (Or.inr rfl), by norm_num, by norm_num, by norm_num,
      Mixed34.endpoints _ (Or.inl rfl), Mixed34.endpoints _ (Or.inr rfl), thirds_readout _ _ Mixed34.convex_not_splits⟩
  · exact ⟨Mixed44.profiles_admissible _ (Or.inl rfl),
      Mixed44.profiles_admissible _ (Or.inr rfl), by norm_num, by norm_num, by norm_num,
      Mixed44.endpoints _ (Or.inl rfl), Mixed44.endpoints _ (Or.inr rfl), halves_readout _ _ Mixed44.convex_not_splits⟩

end LongCycleBounds.CycleProfile
