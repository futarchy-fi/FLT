/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentSource

/-!
# The actual strict-branch subdomain of the divided tangent source

Invert the tangent denominator together with the complementary first branch
factor. Both inverses and the entire map to the tangent chart are constructed
by localization. Flatness preserves regularity of the original scale.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)

/-- The complementary factor selecting the first strict branch. -/
def dividedTangentBranchFactor : S :=
  a (y W s b3 b4 b6) + algebraMap R S W.a₁ * a (x W s b3 b4 b6) + algebraMap R S b3

local notation "D" => dividedTangentDenominator W s b3 b4 b6 a c
local notation "C" => dividedTangentBranchFactor W s b3 b4 b6 a

/-- This is a genuine principal open in the complete divided pair source. -/
def DividedTangentBranchRing := Localization.Away (D * C)

local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "T" => DividedTangentRing W s b3 b4 b6 a c

instance dividedTangentBranchCommRing : CommRing B :=
  inferInstanceAs (CommRing (Localization.Away (D * C)))

instance dividedTangentBranchAlgebraSource : Algebra S B :=
  inferInstanceAs (Algebra S (Localization.Away (D * C)))

instance dividedTangentBranchAlgebra : Algebra R B :=
  inferInstanceAs (Algebra R (Localization.Away (D * C)))

instance dividedTangentBranchTower : IsScalarTower R S B :=
  inferInstanceAs (IsScalarTower R S (Localization.Away (D * C)))

instance dividedTangentBranchLocalization : IsLocalization.Away (D * C) B :=
  inferInstanceAs (IsLocalization.Away (D * C) (Localization.Away (D * C)))

attribute [irreducible] DividedTangentBranchRing

/-- Both actual principal-open factors are invertible in the branch source. -/
theorem dividedTangentBranch_units : IsUnit (algebraMap S B D) ∧ IsUnit (algebraMap S B C) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := B) (D * C)
  rw [map_mul] at h
  exact ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩

/-- The entire original tangent source has a constructed restriction to the branch open. -/
def dividedTangentBranchRestriction : T →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom R S B) D
    (dividedTangentBranch_units W s b3 b4 b6 a c).1

/-- No function of either input is changed by the tangent-source lift. -/
theorem dividedTangentBranchRestriction_source (z : S) :
    dividedTangentBranchRestriction W s b3 b4 b6 a c (algebraMap S T z) =
      algebraMap S B z :=
  IsLocalization.Away.lift_eq D (dividedTangentBranch_units W s b3 b4 b6 a c).1 z

/-- The new source remains flat over the original coefficient ring. -/
instance dividedTangentBranchFlat [Module.Flat R S] : Module.Flat R B := by
  let _ : Module.Flat S B := IsLocalization.flat B (Submonoid.powers (D * C))
  exact Module.Flat.trans R S B

/-- A regular coefficient scale remains regular on the entire constructed branch open. -/
theorem dividedTangentBranch_scale_regular [Module.Flat R S] (hs : IsRegular s) :
    IsRegular (algebraMap R B s) :=
  WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hs

end FLT.Mazur.WeierstrassDilatation
