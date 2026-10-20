/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeBranchSource

/-!
# Three explicit domains cover every original tangent prime

The secant domain, the complementary negative branch, and the swapped
strict branch cover the entire tangent source. This elementary ideal
argument holds before imposing any special-fiber or smoothness condition.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "D" => dividedTangentDenominator W s b3 b4 b6 a c
local notation "E" => dividedTangentDenominator W s b3 b4 b6 c a
local notation "dx" => a (x W s b3 b4 b6) - c (x W s b3 b4 b6)
local notation "y₁" => a (y W s b3 b4 b6)
local notation "C₂" => dividedTangentBranchFactor W s b3 b4 b6 c

/-- The secant difference measures the exact failure of the reversed denominator to agree. -/
theorem dividedTangentDenominator_reverse_difference :
    D = E - algebraMap R S W.a₁ * dx := by
  simp only [dividedTangentDenominator]
  ring

/-- The first ordinate and the swapped branch factor sum to the original tangent denominator. -/
theorem dividedTangentDenominator_branch_sum : D = y₁ + C₂ := by
  simp only [dividedTangentDenominator, dividedTangentBranchFactor]
  ring

/-- Every original tangent prime lies in a secant, complementary, or swapped branch domain. -/
theorem dividedTangent_three_domains (p : PrimeSpectrum S)
    (hp : p ∈ PrimeSpectrum.basicOpen D) :
    p ∈ PrimeSpectrum.basicOpen dx ∨
      p ∈ PrimeSpectrum.basicOpen (E * y₁) ∨
        p ∈ PrimeSpectrum.basicOpen (E * C₂) := by
  classical
  by_cases he : E ∈ p.asIdeal
  · left
    intro hx
    apply hp
    rw [dividedTangentDenominator_reverse_difference]
    exact p.asIdeal.sub_mem he (p.asIdeal.mul_mem_left _ hx)
  · right
    by_cases hy : y₁ ∈ p.asIdeal
    · right
      intro hprod
      rcases p.isPrime.mem_or_mem hprod with h | h
      · exact he h
      · apply hp
        rw [dividedTangentDenominator_branch_sum]
        exact p.asIdeal.add_mem hy h
    · left
      intro hprod
      exact (p.isPrime.mem_or_mem hprod).elim he hy

end FLT.Mazur.WeierstrassDilatation
