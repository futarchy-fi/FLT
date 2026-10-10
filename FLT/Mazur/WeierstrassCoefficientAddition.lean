/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientProductMorphism
public import FLT.Mazur.WeierstrassCoefficientSecant
public import FLT.Mazur.WeierstrassVariableChangeAddition

/-!
# Actual global addition commutes with coefficient extension

The secant coordinate square and schematic density prove compatibility on
the entire proper product. The proof allows nilpotents and arbitrary characteristic.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

local notation "V" => W.map (algebraMap R S)

/-- The global addition retains its actual secant formula in every universe. -/
@[reassoc] theorem integralCurveAddition_secant_restriction (hW : IsUnit W.Δ) :
    Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫
        integralCurveProductChart W false false ≫ integralCurveAddition W hW =
      Spec.map (CommRingCat.ofHom (secantAddition W).toRingHom) ≫ integralCurveChart W 2 := by
  rw [integralCurveProductChart_affine_addition]
  exact additionCurveChart_glued W hW .secant

/-- Coefficient extension commutes with restriction to the actual secant open. -/
theorem secantCoefficientMap_spec_restriction :
    Spec.map (CommRingCat.ofHom (secantRestriction V).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (affineProductCoefficientMap W).toRingHom) =
      Spec.map (CommRingCat.ofHom (secantCoefficientMap (S := S) W).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  exact (secantCoefficientMap_restriction (S := S) W a).symm

/-- The actual global addition is compatible with every coefficient extension. -/
@[reassoc] theorem integralCoefficientMorphism_addition
    (hW : IsUnit W.Δ) (hV : IsUnit (V).Δ) :
    integralCurveAddition V hV ≫ integralCoefficientMorphism W =
      integralCoefficientProduct (S := S) W ≫ integralCurveAddition W hW := by
  apply integralCurveProduct_hom_ext_secant V (integralCurveStructure W)
  · simp only [Category.assoc, integralCoefficientMorphism_structure,
      integralCurveAddition_structure,
      integralCoefficientProduct_fst_assoc]
    rw [← Category.assoc, integralCurveAddition_structure, Category.assoc]
  · slice_lhs 1 3 => rw [integralCurveAddition_secant_restriction]
    rw [Category.assoc, integralCurveChart_coefficientMorphism]
    slice_rhs 2 3 => rw [integralCoefficientProduct_affine]
    slice_rhs 1 2 => rw [secantCoefficientMap_spec_restriction]
    slice_rhs 2 4 => rw [integralCurveAddition_secant_restriction]
    simp only [← Category.assoc]
    apply congrArg (· ≫ integralCurveChart W 2)
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (secantCoefficientMap_addition (S := S) W).symm

end FLT.Mazur.WeierstrassIntegralChart
