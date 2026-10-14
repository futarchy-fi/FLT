/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingReciprocalScaling
public import FLT.Mazur.PolygonSmoothingOverlapGraph
public import FLT.Mazur.PolygonSmoothingMarkedSection
public import FLT.Mazur.LaurentScaledCoordinateIsomorphisms

/-!
# Reciprocal scaling on the full arithmetic branch overlaps

The two full punctured-branch squares commute, with the inverse coordinate
on the incoming edge. Thus the arithmetic scalings can be glued on the
original infinitesimal cyclic atlas.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)

/-- Scaling restricts to the original Laurent scaling on the outgoing branch. -/
theorem leftLaurentMap_reciprocalScale (a : Rˣ) :
    (leftLaurentMap t).comp (reciprocalScale t a) =
      (PolygonScaledReciprocal.scaling a).comp (leftLaurentMap t) := by
  apply chartRing_hom_ext t <;>
    simp [PolygonScaledReciprocal.scaling, AlgHom.coe_mk, mul_left_comm]

/-- The incoming inverse coordinate has the same full Laurent scaling. -/
theorem precedingLaurentMap_reciprocalScale (a : Rˣ) :
    (precedingLaurentMap R t).comp (reciprocalScale t a) =
      (PolygonScaledReciprocal.scaling a).comp (precedingLaurentMap R t) := by
  apply chartRing_hom_ext t <;>
    simp [precedingLaurentMap, PolygonScaledReciprocal.scaling, AlgHom.coe_mk, mul_left_comm]

/-- The actual arithmetic chart automorphism at a coefficient unit. -/
def reciprocalScalingIso (a : Rˣ) : chart R t ≅ chart R t :=
  Scheme.Spec.mapIso (reciprocalScaleEquiv t a).toRingEquiv.toCommRingCatIso.op

/-- The common full edge automorphism. -/
def edgeScalingIso (a : Rˣ) : branchTorus R ≅ branchTorus R :=
  Scheme.Spec.mapIso (PolygonScaledReciprocal.scalingEquiv a).toRingEquiv.toCommRingCatIso.op

/-- The outgoing original branch square commutes as a square of schemes. -/
@[reassoc] theorem leftBranch_reciprocalScaling (a : Rˣ) :
    leftBranchOpen R t ≫ (reciprocalScalingIso t a).hom =
      (edgeScalingIso a).hom ≫ leftBranchOpen R t := by
  rw [leftBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (leftLaurentMap_reciprocalScale t a))

/-- The incoming original branch square retains its inverse coordinate. -/
@[reassoc] theorem precedingBranch_reciprocalScaling (a : Rˣ) :
    precedingBranch R t ≫ (reciprocalScalingIso t a).hom =
      (edgeScalingIso a).hom ≫ precedingBranch R t := by
  rw [precedingBranch_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (precedingLaurentMap_reciprocalScale t a))

/-- Reciprocal scaling preserves the actual arithmetic base morphism. -/
@[reassoc] theorem reciprocalScalingIso_base (a : Rˣ) :
    (reciprocalScalingIso t a).hom ≫ chartStructure R t = chartStructure R t := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (reciprocalScale t a).comp_algebraMap

/-- The identity parameter gives the identity arithmetic chart morphism. -/
@[simp] theorem reciprocalScalingIso_one : (reciprocalScalingIso t 1).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (reciprocalScale t 1).toRingHom) = _
  rw [reciprocalScale_one]
  exact Spec.map_id _

/-- The full arithmetic chart maps obey multiplication of units. -/
theorem reciprocalScalingIso_mul (a b : Rˣ) :
    (reciprocalScalingIso t (a * b)).hom =
      (reciprocalScalingIso t a).hom ≫ (reciprocalScalingIso t b).hom := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (reciprocalScale_mul t a b)

/-- Every original unit marking is sent to the marking with multiplied coordinate. -/
@[reassoc] theorem markedSection_reciprocalScaling (a b : Rˣ) :
    markedSection t b ≫ (reciprocalScalingIso t a).hom = markedSection t (a * b) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change ((markedEvaluation t b).comp (reciprocalScale t a)).toRingHom =
    (markedEvaluation t (a * b)).toRingHom
  apply congrArg AlgHom.toRingHom
  apply chartRing_hom_ext t <;> simp [mul_left_comm, mul_comm]

end FLT.Mazur.PolygonSmoothing
