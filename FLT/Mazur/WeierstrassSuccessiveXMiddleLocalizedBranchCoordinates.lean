/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleLocalizedPushout

/-!
# Original functions on the localized normalization branches

These are the ring maps defining the proved scheme pushout. They preserve the
actual node coordinates, rather than only identifying the component point sets.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (c : K)
local notation "s" => middleNodePairDenominator c
local notation "L" => MiddleNodeOpen c
local notation "B₁" => Localization.Away (PolygonNodeEqualizer.first s)
local notation "B₂" => Localization.Away (PolygonNodeEqualizer.second s)

/-- Restriction to the conic branch of the actual localized node. -/
def middleLocalizedFirstRestriction : L →+* B₁ :=
  (RingHom.fst _ _).comp ((MiddleNodeEqualizer c).subtype.comp
    (middleNodeEqualizerEquiv c).toRingHom)

/-- Restriction to the whole original horizontal branch. -/
def middleLocalizedSecondRestriction : L →+* B₂ :=
  (RingHom.snd _ _).comp ((MiddleNodeEqualizer c).subtype.comp
    (middleNodeEqualizerEquiv c).toRingHom)

/-- First restriction agrees with the original polynomial-pair coordinates. -/
theorem middleLocalizedFirstRestriction_base (x : SuccessiveIncidence.Coordinate (0 : K)) :
    middleLocalizedFirstRestriction c (algebraMap _ L x) =
      algebraMap K[X] B₁ (PolygonNodeEqualizer.first (NodalFiber.polygonNodeEquiv x)) := by
  change (middleNodeEqualizerEquiv c (algebraMap _ L x)).val.1 = _
  rw [middleNodeEqualizerEquiv_base]
  rfl

/-- Second restriction agrees with the original polynomial-pair coordinates. -/
theorem middleLocalizedSecondRestriction_base (x : SuccessiveIncidence.Coordinate (0 : K)) :
    middleLocalizedSecondRestriction c (algebraMap _ L x) =
      algebraMap K[X] B₂ (PolygonNodeEqualizer.second (NodalFiber.polygonNodeEquiv x)) := by
  change (middleNodeEqualizerEquiv c (algebraMap _ L x)).val.2 = _
  rw [middleNodeEqualizerEquiv_base]
  rfl

/-- The incidence presentation retains the first ordered polynomial-pair coordinate. -/
theorem middleLocalizedPair_z :
    NodalFiber.polygonNodeEquiv (SuccessiveIncidence.t (0 : K)) =
      PolygonNodeLocalization.x := NodalFiber.polygonNodeEquiv_p

/-- The incidence presentation retains the second ordered polynomial-pair coordinate. -/
theorem middleLocalizedPair_u :
    NodalFiber.polygonNodeEquiv (SuccessiveIncidence.u (0 : K)) =
      PolygonNodeLocalization.y := NodalFiber.polygonNodeEquiv_q

/-- The conic branch retains the original node parameter. -/
@[simp] theorem middleLocalizedFirstRestriction_z :
    middleLocalizedFirstRestriction c (middleNodeZ c) = algebraMap K[X] B₁ X := by
  rw [middleNodeZ, middleLocalizedFirstRestriction_base, middleLocalizedPair_z,
    PolygonNodeLocalization.first_x]

/-- The conic branch kills exactly the other node coordinate. -/
@[simp] theorem middleLocalizedFirstRestriction_u :
    middleLocalizedFirstRestriction c (middleNodeU c) = 0 := by
  rw [middleNodeU, middleLocalizedFirstRestriction_base, middleLocalizedPair_u,
    PolygonNodeLocalization.first_y, map_zero]

/-- The incidence branch kills the original node parameter. -/
@[simp] theorem middleLocalizedSecondRestriction_z :
    middleLocalizedSecondRestriction c (middleNodeZ c) = 0 := by
  rw [middleNodeZ, middleLocalizedSecondRestriction_base, middleLocalizedPair_z,
    PolygonNodeLocalization.second_x, map_zero]

/-- The incidence branch retains the original horizontal coordinate. -/
@[simp] theorem middleLocalizedSecondRestriction_u :
    middleLocalizedSecondRestriction c (middleNodeU c) = algebraMap K[X] B₂ X := by
  rw [middleNodeU, middleLocalizedSecondRestriction_base, middleLocalizedPair_u,
    PolygonNodeLocalization.second_y]

/-- The first restriction induces exactly the first branch of the scheme pushout. -/
theorem middleNodeLocalizedFirstBranch_eq_spec : middleNodeLocalizedFirstBranch c =
    Spec.map (CommRingCat.ofHom (middleLocalizedFirstRestriction c)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The second restriction induces exactly the second branch of the scheme pushout. -/
theorem middleNodeLocalizedSecondBranch_eq_spec : middleNodeLocalizedSecondBranch c =
    Spec.map (CommRingCat.ofHom (middleLocalizedSecondRestriction c)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
