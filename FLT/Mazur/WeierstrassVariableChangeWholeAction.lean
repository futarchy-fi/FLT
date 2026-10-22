/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeLeftSmoothProduct
public import FLT.Mazur.WeierstrassLeftSmoothCoefficientAddition
public import FLT.Mazur.WeierstrassSmoothWholeAction

/-!
# Admissible changes preserve the whole action on singular cubics

The second input is unrestricted. Secant descent proves compatibility of the
actual smooth-by-whole addition maps over every coefficient ring, including
nonreduced mixed-characteristic bases.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)
local notation "e" => integralVariableChangeSmoothMap W V C h
local notation "E" => integralVariableChangeIso W V C h

/-- On every secant test, the enlarged comparison preserves the original sum. -/
theorem integralVariableChangeLeftSmoothProduct_secant {U : Scheme}
    (p : U ⟶ leftSmoothFactorProduct V) (a : U ⟶ Spec (.of (SecantChart V)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (secantRestriction V).toRingHom) ≫
      integralCurveProductChart V false false = p ≫ leftSmoothFactorsInclusion V) :
    p ≫ leftSmoothFactorAddition V ≫ (E).hom =
      p ≫ integralVariableChangeLeftSmoothProduct W V C h ≫ leftSmoothFactorAddition W := by
  have hl := leftSmoothFactorAddition_secant V p a ha
  have hr := leftSmoothFactorAddition_secant W
    (p ≫ integralVariableChangeLeftSmoothProduct W V C h)
    (a ≫ Spec.map (CommRingCat.ofHom (secantVariableChange W V C h).toRingHom)) (by
      rw [Category.assoc, secantVariableChange_globalDomain, ← Category.assoc, ha]
      simp only [Category.assoc, integralVariableChangeLeftSmoothProduct_inclusion])
  rw [← Category.assoc p, hl, Category.assoc, Category.assoc,
    integralVariableChangeIso_affine]
  rw [← Category.assoc p, hr]
  simp only [← Category.assoc]
  apply congrArg (· ≫ integralCurveChart W 2)
  simp only [Category.assoc]
  apply congrArg (a ≫ ·)
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (secantVariableChange_addition W V C h).symm

/-- The enlarged input inclusion is flat over the original proper product. -/
theorem leftSmoothFactorsInclusion_flat (V : WeierstrassCurve R) :
    Flat (leftSmoothFactorsInclusion V) := by
  rw [← leftSmoothFactorsToProduct_inclusion]
  let _ : IsIso (leftSmoothFactorsToProduct V) :=
    (leftSmoothProductFactorsIso V).symm.isIso_hom
  infer_instance

/-- Admissible changes preserve addition with an arbitrary second point of the cubic. -/
@[reassoc] theorem integralVariableChangeLeftSmoothProduct_addition :
    leftSmoothFactorAddition V ≫ (E).hom =
      integralVariableChangeLeftSmoothProduct W V C h ≫ leftSmoothFactorAddition W := by
  let _ := leftSmoothFactorsInclusion_flat V
  apply flatProduct_hom_ext_secant V (leftSmoothFactorsInclusion V) (integralCurveStructure W)
  · simp only [Category.assoc]
    change leftSmoothFactorAddition V ≫ integralVariableChangeTo W V C h ≫
      integralCurveStructure W = _
    rw [integralVariableChangeTo_structure]
    simp only [leftSmoothFactorAddition_structure,
      integralVariableChangeLeftSmoothProduct_fst_assoc,
      integralVariableChangeSmoothMap_structure]
  · intro U p a ha
    exact integralVariableChangeLeftSmoothProduct_secant W V C h p a ha

/-- The entire intrinsic group action commutes with every admissible coordinate change. -/
theorem integralVariableChangeOverIso_wholeAction :
    integralSmoothWholeAction V ≫ (integralVariableChangeOverIso W V C h).hom =
      ((integralVariableChangeSmoothOverIso W V C h).hom ⊗ₘ
        (integralVariableChangeOverIso W V C h).hom) ≫ integralSmoothWholeAction W := by
  apply Over.OverMorphism.ext
  change leftSmoothFactorAddition V ≫ (E).hom = _ ≫ leftSmoothFactorAddition W
  exact (integralVariableChangeLeftSmoothProduct_addition W V C h).trans
    (congrArg (· ≫ leftSmoothFactorAddition W)
      (integralVariableChangeLeftSmoothProduct_tensor W V C h)).symm

end FLT.Mazur.WeierstrassIntegralChart
