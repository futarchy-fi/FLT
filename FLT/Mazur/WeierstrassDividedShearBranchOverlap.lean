/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearBranchSource

/-!
# Construct the common domain of a normalized branch and the original tangent

The common source is an actual principal localization of the original
input algebra. Both comparison maps are constructed from its inverted
factors and retain every function of the original two inputs.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "V" => rootShearCurve W r
local notation "a'" => branchShearInput W s b3 b4 b6 r a
local notation "c'" => branchShearInput W s b3 b4 b6 r c
local notation "D" => dividedTangentDenominator W s b3 b4 b6 a c
local notation "N" => dividedTangentDenominator V s b3 (b4 - r * b3) b6 a' c' *
  dividedTangentBranchFactor V s b3 (b4 - r * b3) b6 a'
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "B" => DividedTangentBranchRing V s b3 (b4 - r * b3) b6 a' c'

/-- The actual common principal open, before any smoothness restriction. -/
def DividedShearBranchOverlap := Localization.Away (D * N)

local notation "O" => DividedShearBranchOverlap W s b3 b4 b6 r a c

instance dividedShearBranchOverlapCommRing : CommRing O :=
  inferInstanceAs (CommRing (Localization.Away (D * N)))

instance dividedShearBranchOverlapAlgebraSource : Algebra S O :=
  inferInstanceAs (Algebra S (Localization.Away (D * N)))

instance dividedShearBranchOverlapAlgebra : Algebra R O :=
  inferInstanceAs (Algebra R (Localization.Away (D * N)))

instance dividedShearBranchOverlapTower : IsScalarTower R S O :=
  inferInstanceAs (IsScalarTower R S (Localization.Away (D * N)))

instance dividedShearBranchOverlapLocalization : IsLocalization.Away (D * N) O :=
  inferInstanceAs (IsLocalization.Away (D * N) (Localization.Away (D * N)))

attribute [irreducible] DividedShearBranchOverlap

/-- Both comparison denominators are units on the constructed common open. -/
theorem dividedShearBranchOverlap_units :
    IsUnit (algebraMap S O D) ∧ IsUnit (algebraMap S O N) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := O) (D * N)
  rw [map_mul] at h
  exact ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩

/-- The entire original tangent source restricts to this actual common domain. -/
def dividedShearBranchOverlapOriginal : T →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom R S O) D
    (dividedShearBranchOverlap_units W s b3 b4 b6 r a c).1

/-- The entire sheared branch source restricts to the same common domain. -/
def dividedShearBranchOverlapNormalized : B →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom R S O) N
    (dividedShearBranchOverlap_units W s b3 b4 b6 r a c).2

/-- The original tangent comparison keeps every original input function. -/
theorem dividedShearBranchOverlapOriginal_source (z : S) :
    dividedShearBranchOverlapOriginal W s b3 b4 b6 r a c (algebraMap S T z) =
      algebraMap S O z :=
  IsLocalization.Away.lift_eq D (dividedShearBranchOverlap_units W s b3 b4 b6 r a c).1 z

/-- The normalized branch comparison keeps the same original input function. -/
theorem dividedShearBranchOverlapNormalized_source (z : S) :
    dividedShearBranchOverlapNormalized W s b3 b4 b6 r a c (algebraMap S B z) =
      algebraMap S O z :=
  IsLocalization.Away.lift_eq N (dividedShearBranchOverlap_units W s b3 b4 b6 r a c).2 z

/-- Flat original sources remain flat after taking the common branch domain. -/
instance dividedShearBranchOverlapFlat [Module.Flat R S] : Module.Flat R O := by
  let _ : Module.Flat S O := IsLocalization.flat O (Submonoid.powers (D * N))
  exact Module.Flat.trans R S O

end FLT.Mazur.WeierstrassDilatation
