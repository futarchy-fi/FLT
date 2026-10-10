/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeProductMorphism
public import FLT.Mazur.WeierstrassVariableChangeSecantAddition
public import FLT.Mazur.WeierstrassSecantMorphismExt
public import FLT.Mazur.WeierstrassGlobalAffineSwap
public import FLT.Mazur.WeierstrassAdditionStructure
public import FLT.Mazur.WeierstrassIntegralSeparated

/-!
# Proper admissible changes commute with the actual global addition

The coordinate-algebra square proves the claim on the actual secant open.
Schematic density extends it to the entire original proper product over any
coefficient ring with unit discriminant, retaining all nilpotents.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

/-- The actual localized product square commutes as scheme morphisms. -/
theorem secantVariableChange_spec_restriction :
    Spec.map (CommRingCat.ofHom (secantRestriction V).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (affineProductVariableChange W V C h).toRingHom) =
      Spec.map (CommRingCat.ofHom (secantVariableChange W V C h).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  exact (secantVariableChange_restriction W V C h a).symm

/-- Global addition retains the actual secant chart formula. -/
@[reassoc] theorem integralCurveAddition_secant (hW : IsUnit W.Δ) :
    Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫
        integralCurveProductChart W false false ≫ integralCurveAddition W hW =
      Spec.map (CommRingCat.ofHom (secantAddition W).toRingHom) ≫ integralCurveChart W 2 := by
  rw [integralCurveProductChart_affine_addition]
  exact additionCurveChart_glued W hW .secant

/-- The actual global addition commutes with every integral admissible change. -/
@[reassoc] theorem integralVariableChangeIso_addition (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    integralCurveAddition V hV ≫ (integralVariableChangeIso W V C h).hom =
      integralVariableChangeProduct W V C h ≫ integralCurveAddition W hW := by
  apply integralCurveProduct_hom_ext_secant V (integralCurveStructure W)
  · simp only [Category.assoc, integralVariableChangeIso,
      integralVariableChangeTo_structure, integralCurveAddition_structure,
      integralVariableChangeProduct_fst_assoc]
  · slice_lhs 1 3 => rw [integralCurveAddition_secant]
    rw [Category.assoc, integralVariableChangeIso_affine]
    slice_rhs 2 3 => rw [integralVariableChangeProduct_affine]
    slice_rhs 1 2 => rw [secantVariableChange_spec_restriction]
    slice_rhs 2 4 => rw [integralCurveAddition_secant]
    simp only [← Category.assoc]
    apply congrArg (· ≫ integralCurveChart W 2)
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (secantVariableChange_addition W V C h).symm

end FLT.Mazur.WeierstrassIntegralChart
