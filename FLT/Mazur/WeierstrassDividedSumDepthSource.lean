/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalDepthSecant
public import FLT.Mazur.WeierstrassDividedTangentBranchSource

/-!
# The actual principal open for same-branch unequal-depth sums

Invert the secant difference, both uncontracted abscissae, and the two
own-depth complementary branch factors. The resulting ring is flat and
receives the entire original unequal-depth secant algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k l : ℕ} (d : Data W π k) (e : Data W π l)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => c (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₂" => c (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "t" => algebraMap R S (π ^ (l - k))
local notation "C₁" => dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a
local notation "C₂" => dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 c

/-- The complete product of input denominators used by the sum-depth construction. -/
def sumDepthSourceDenominator : S := (x₁ - t * x₂) * (x₁ * x₂) * C₁ * C₂

local notation "D" => sumDepthSourceDenominator d e a c

/-- An actual principal open in the full unequal-depth pair source. -/
def SumDepthSourceRing := Localization.Away D

local notation "B" => SumDepthSourceRing d e a c

instance sumDepthSourceCommRing : CommRing B := inferInstanceAs (CommRing (Localization.Away D))

instance sumDepthSourceAlgebraSource : Algebra S B :=
  inferInstanceAs (Algebra S (Localization.Away D))

instance sumDepthSourceAlgebra : Algebra R B :=
  inferInstanceAs (Algebra R (Localization.Away D))

instance sumDepthSourceTower : IsScalarTower R S B :=
  inferInstanceAs (IsScalarTower R S (Localization.Away D))

instance sumDepthSourceLocalization : IsLocalization.Away D B :=
  inferInstanceAs (IsLocalization.Away D (Localization.Away D))

attribute [irreducible] SumDepthSourceRing

/-- All four actual input factors are units on the constructed source. -/
theorem sumDepthSource_units :
    IsUnit (algebraMap S B (x₁ - t * x₂)) ∧ IsUnit (algebraMap S B (x₁ * x₂)) ∧
      IsUnit (algebraMap S B C₁) ∧ IsUnit (algebraMap S B C₂) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := B) D
  unfold sumDepthSourceDenominator at h
  rw [map_mul, map_mul, map_mul] at h
  have h₁ := isUnit_of_mul_isUnit_left h
  have h₂ := isUnit_of_mul_isUnit_left h₁
  exact ⟨isUnit_of_mul_isUnit_left h₂, isUnit_of_mul_isUnit_right h₂,
    isUnit_of_mul_isUnit_right h₁, isUnit_of_mul_isUnit_right h⟩

/-- Localization preserves flatness over the original coefficients. -/
instance sumDepthSourceFlat [Module.Flat R S] : Module.Flat R B := by
  let _ : Module.Flat S B := IsLocalization.flat B (Submonoid.powers D)
  exact Module.Flat.trans R S B

open AlgebraicGeometry CategoryTheory

/-- The constructed source is an actual open in the full original input spectrum. -/
def sumDepthSourceInclusion : Spec (.of B) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S B))

instance sumDepthSourceInclusion_open : IsOpenImmersion (sumDepthSourceInclusion d e a c) :=
  IsOpenImmersion.of_isLocalization D

variable [IsDomain R] (hπ : π ≠ 0) (hkl : k ≤ l)
local notation "c₀" => unequalDepthRight hπ d e hkl c
local notation "T" => UnequalDepthSecantRing hπ d e hkl a c
local notation "dx" => x₁ - c₀ (x W (π ^ k) d.b3 d.b4 d.b6)

/-- The secant denominator is a unit under the actual coefficient algebra map. -/
theorem sumDepthSource_secantUnit : IsUnit ((IsScalarTower.toAlgHom R S B) dx) := by
  simpa only [unequalDepthRight_x, IsScalarTower.coe_toAlgHom'] using
    (sumDepthSource_units d e a c).1

/-- The original entire secant algebra restricts to the new branch principal open. -/
def sumDepthSourceRestriction : T →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom R S B) dx
    (sumDepthSource_secantUnit d e a c hπ hkl)

/-- Every original input function is retained by this restriction. -/
theorem sumDepthSourceRestriction_source (v : S) :
    sumDepthSourceRestriction d e a c hπ hkl (algebraMap S T v) = algebraMap S B v :=
  IsLocalization.Away.lift_eq dx (sumDepthSource_secantUnit d e a c hπ hkl) v

local notation "res" => sumDepthSourceRestriction d e a c hπ hkl
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "a'" => (j).comp a
local notation "c'" => (j).comp c

/-- The secant inverse is constructed by restricting the original localization inverse. -/
def sumDepthSourceInverse : B := res (IsLocalization.Away.invSelf dx)

/-- The original secant slope is retained on the new source. -/
def sumDepthSourceSlope : B :=
  res (dividedSecantSlope W (π ^ k) d.b3 d.b4 d.b6 a c₀)

/-- The constructed inverse satisfies the required equation in the actual source ring. -/
theorem sumDepthSourceInverse_relation :
    sumDepthSourceInverse d e a c hπ hkl *
      ((a') (x W (π ^ k) d.b3 d.b4 d.b6) - algebraMap R B (π ^ (l - k)) *
        (c') (x W (π ^ l) e.b3 e.b4 e.b6)) = 1 := by
  have h := congrArg res (unequalDepthSecant_inverse hπ d e hkl a c)
  simpa only [sumDepthSourceInverse, map_mul, map_sub, map_one, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', AlgHom.commutes, sumDepthSourceRestriction_source] using h

/-- The same slope satisfies the original divided chord relation on this source. -/
theorem sumDepthSourceSlope_relation :
    sumDepthSourceSlope d e a c hπ hkl *
      ((a') (x W (π ^ k) d.b3 d.b4 d.b6) - algebraMap R B (π ^ (l - k)) *
        (c') (x W (π ^ l) e.b3 e.b4 e.b6)) =
      (a') (y W (π ^ k) d.b3 d.b4 d.b6) - algebraMap R B (π ^ (l - k)) *
        (c') (y W (π ^ l) e.b3 e.b4 e.b6) := by
  have h := congrArg res (unequalDepthSecant_chord hπ d e hkl a c)
  simpa only [sumDepthSourceSlope, map_mul, map_sub, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', AlgHom.commutes, sumDepthSourceRestriction_source] using h

end FLT.Mazur.WeierstrassDividedDepth
