/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothCoefficientProduct
public import FLT.Mazur.WeierstrassSmoothCoefficientAddition
public import FLT.Mazur.WeierstrassLeftSmoothFormulaComparison

/-!
# The whole smooth action commutes with arbitrary coefficient change

Secant descent compares the actual smooth-by-whole addition morphisms. The
second input is unrestricted, so this also retains the action on singular
points over arbitrary coefficient rings, including nonreduced rings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)
local notation "V" => W.map (algebraMap R S)

/-- A secant presentation computes the enlarged sum with its unrestricted second input. -/
theorem leftSmoothFactorAddition_secant {T : Scheme.{u}} (p : T ⟶ leftSmoothFactorProduct W)
    (a : T ⟶ Spec (.of (SecantChart W)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫
      integralCurveProductChart W false false = p ≫ leftSmoothFactorsInclusion W) :
    p ≫ leftSmoothFactorAddition W =
      a ≫ Spec.map (CommRingCat.ofHom (secantAddition W).toRingHom) ≫
        integralCurveChart W 2 :=
  leftSmoothFactorAddition_chart W p .secant a ha

/-- The actual smooth-by-whole addition commutes with every coefficient extension. -/
@[reassoc] theorem originalLeftSmoothCoefficientMap_addition :
    leftSmoothFactorAddition V ≫ integralCoefficientMorphism W =
      originalLeftSmoothCoefficientProduct S W ≫ leftSmoothFactorAddition W := by
  let _ : Flat (leftSmoothFactorsInclusion V) := by
    rw [← leftSmoothFactorsToProduct_inclusion]
    let _ : IsIso (leftSmoothFactorsToProduct V) :=
      (leftSmoothProductFactorsIso V).symm.isIso_hom
    infer_instance
  apply flatProduct_hom_ext_secant V (leftSmoothFactorsInclusion V) (integralCurveStructure W)
  · rw [Category.assoc, integralCoefficientMorphism_structure,
      ← Category.assoc, leftSmoothFactorAddition_structure]
    simp only [Category.assoc, leftSmoothFactorAddition_structure,
      originalLeftSmoothCoefficientProduct_fst_assoc,
      originalSmoothCoefficientMap_structure]
  · intro U p a ha
    have hl := leftSmoothFactorAddition_secant V p a ha
    have hr := leftSmoothFactorAddition_secant W
      (p ≫ originalLeftSmoothCoefficientProduct S W)
      (a ≫ Spec.map
        (CommRingCat.ofHom (secantCoefficientMap (S := S) W).toRingHom)) (by
          rw [Category.assoc, secantCoefficientMap_globalDomain, ← Category.assoc, ha]
          simp only [Category.assoc, originalLeftSmoothCoefficientProduct_inclusion])
    rw [← Category.assoc p, hl, Category.assoc, Category.assoc,
      integralCurveChart_coefficientMorphism]
    rw [← Category.assoc p, hr]
    change a ≫ Spec.map (CommRingCat.ofHom (secantAddition V).toRingHom) ≫
        chartCoefficientMorphism W 2 ≫ integralCurveChart W 2 =
      (a ≫ Spec.map (CommRingCat.ofHom (secantCoefficientMap (S := S) W).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (secantAddition W).toRingHom) ≫ integralCurveChart W 2
    simp only [← Category.assoc]
    apply congrArg (· ≫ integralCurveChart W 2)
    simp only [Category.assoc]
    apply congrArg (a ≫ ·)
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
      (secantCoefficientMap_addition (S := S) W).symm

end FLT.Mazur.WeierstrassDividedDepth
