/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodePushout

/-!
# Original functions on the localized normalization branches

These are the ring maps defining the proved scheme pushout. They preserve the
actual node coordinates, rather than only identifying the component point sets.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (a c : K) (ha : IsUnit a)
local notation "s" => fullNodeNormalizedDenominator a c
local notation "L" => FullNodeOpen a c
local notation "B₁" => Localization.Away (PolygonNodeEqualizer.first s)
local notation "B₂" => Localization.Away (PolygonNodeEqualizer.second s)

/-- Restriction to the conic branch of the actual localized node. -/
def fullNodeFirstRestriction : L →+* B₁ :=
  (RingHom.fst _ _).comp ((FullNodeEqualizer a c ha).subtype.comp
    (fullNodeEqualizerEquiv a c ha).toRingHom)

/-- Restriction to the incidence branch, retaining its tangent denominator. -/
def fullNodeSecondRestriction : L →+* B₂ :=
  (RingHom.snd _ _).comp ((FullNodeEqualizer a c ha).subtype.comp
    (fullNodeEqualizerEquiv a c ha).toRingHom)

/-- First restriction agrees with the original polynomial-pair coordinates. -/
theorem fullNodeFirstRestriction_base (x : NodalFiber.Coordinate (0 : K)) :
    fullNodeFirstRestriction a c ha (algebraMap _ L x) =
      algebraMap K[X] B₁ (PolygonNodeEqualizer.first (NodalFiber.polygonNodeEquiv x)) := by
  change (fullNodeEqualizerEquiv a c ha (algebraMap _ L x)).val.1 = _
  rw [fullNodeEqualizerEquiv_base]
  rfl

/-- Second restriction agrees with the original polynomial-pair coordinates. -/
theorem fullNodeSecondRestriction_base (x : NodalFiber.Coordinate (0 : K)) :
    fullNodeSecondRestriction a c ha (algebraMap _ L x) =
      algebraMap K[X] B₂ (PolygonNodeEqualizer.second (NodalFiber.polygonNodeEquiv x)) := by
  change (fullNodeEqualizerEquiv a c ha (algebraMap _ L x)).val.2 = _
  rw [fullNodeEqualizerEquiv_base]
  rfl

/-- The conic branch retains the original node parameter. -/
@[simp] theorem fullNodeFirstRestriction_p :
    fullNodeFirstRestriction a c ha (fullNodeP a c) = algebraMap K[X] B₁ X := by
  rw [fullNodeP, fullNodeFirstRestriction_base, NodalFiber.polygonNodeEquiv_p,
    PolygonNodeLocalization.first_x]

/-- The conic branch kills exactly the other node coordinate. -/
@[simp] theorem fullNodeFirstRestriction_q :
    fullNodeFirstRestriction a c ha (fullNodeQ a c) = 0 := by
  rw [fullNodeQ, fullNodeFirstRestriction_base, NodalFiber.polygonNodeEquiv_q,
    PolygonNodeLocalization.first_y, map_zero]

/-- The incidence branch kills the original node parameter. -/
@[simp] theorem fullNodeSecondRestriction_p :
    fullNodeSecondRestriction a c ha (fullNodeP a c) = 0 := by
  rw [fullNodeP, fullNodeSecondRestriction_base, NodalFiber.polygonNodeEquiv_p,
    PolygonNodeLocalization.second_x, map_zero]

/-- The incidence branch retains the original slope coordinate. -/
@[simp] theorem fullNodeSecondRestriction_q :
    fullNodeSecondRestriction a c ha (fullNodeQ a c) = algebraMap K[X] B₂ X := by
  rw [fullNodeQ, fullNodeSecondRestriction_base, NodalFiber.polygonNodeEquiv_q,
    PolygonNodeLocalization.second_y]

/-- The first restriction induces exactly the first branch of the scheme pushout. -/
theorem fullNodeFirstBranch_eq_spec : fullNodeFirstBranch a c ha =
    Spec.map (CommRingCat.ofHom (fullNodeFirstRestriction a c ha)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The second restriction induces exactly the second branch of the scheme pushout. -/
theorem fullNodeSecondBranch_eq_spec : fullNodeSecondBranch a c ha =
    Spec.map (CommRingCat.ofHom (fullNodeSecondRestriction a c ha)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
