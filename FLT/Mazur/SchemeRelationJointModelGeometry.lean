/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationJointModel
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Geometry and coefficient detection for joint finite models

The joint projection detects maps to affine schemes because its coefficient
inclusion is injective. Finite type of a source projection to either retained
model gives finite presentation to the Noetherian joint target.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationJointModel
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {E A : Scheme.{u}} (p q : E ⟶ A)
  {C D : Type u} [CommRing C] [CommRing D]
  (c : C →+* compatibleFunctions p q) (d : D →+* compatibleFunctions p q)

/-- Normalized pullback is the literal inclusion of joint invariant coefficients. -/
theorem projection_coefficients :
    (Scheme.ΓSpecIso (.of (FiniteCoefficientJoin.algebra c d))).inv ≫
      (projection p q c d).appTop =
        CommRingCat.ofHom ((compatibleFunctions p q).subtype.comp
          (FiniteCoefficientJoin.inclusion c d)) := by
  rw [projection, fromInvariants, SchemeRelationInvariantSpectrum.projection,
    Category.assoc, ← Spec.map_comp]
  exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

/-- The joint target has no coefficient functions invisible on the actual source. -/
theorem projection_appTop_injective : Function.Injective (projection p q c d).appTop := by
  have h : (projection p q c d).appTop =
      (Scheme.ΓSpecIso (.of (FiniteCoefficientJoin.algebra c d))).hom ≫
        CommRingCat.ofHom ((compatibleFunctions p q).subtype.comp
          (FiniteCoefficientJoin.inclusion c d)) := by
    rw [← Iso.inv_comp_eq]
    exact projection_coefficients p q c d
  rw [h]
  exact (Subtype.val_injective.comp Subtype.val_injective).comp
    (Scheme.ΓSpecIso (.of (FiniteCoefficientJoin.algebra c d))).commRingCatIsoToRingEquiv.injective

/-- Agreement on the original source detects affine-valued maps from the joint target. -/
theorem affine_hom_ext {Y : Scheme.{u}} [IsAffine Y] {g h : target p q c d ⟶ Y}
    (he : projection p q c d ≫ g = projection p q c d ≫ h) : g = h := by
  apply ext_of_isAffine
  ext s
  apply projection_appTop_injective p q c d
  exact congrArg (fun z ↦ z.appTop s) he

/-- Source finite type over the second model survives the constructed coefficient enlargement. -/
instance projection_locallyOfFiniteType
    [LocallyOfFiniteType (coefficientProjection p q d)] :
    LocallyOfFiniteType (projection p q c d) := by
  have : LocallyOfFiniteType (projection p q c d ≫ toRight p q c d) := by
    rw [projection_toRight]
    infer_instance
  exact locallyOfFiniteType_of_comp (projection p q c d) (toRight p q c d)

/-- Actual finite presentation follows from Noetherianity of the constructed joint target. -/
instance projection_locallyOfFinitePresentation
    [Algebra.FiniteType ℤ C] [Algebra.FiniteType ℤ D]
    [LocallyOfFiniteType (coefficientProjection p q d)] :
    LocallyOfFinitePresentation (projection p q c d) := by infer_instance

end FLT.Mazur.SchemeRelationJointModel
