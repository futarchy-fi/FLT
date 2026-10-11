/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientProduct
public import FLT.Mazur.WeierstrassFlatProductSecantDescent
public import FLT.Mazur.WeierstrassCoefficientAddition

/-!
# Smooth addition commutes with arbitrary coefficient extension

Flat secant descent compares the actual smooth addition maps. The argument
uses the original secant formulas, without a good-reduction hypothesis.
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

/-- The coefficient secant chart retains its two actual global inputs. -/
@[reassoc] theorem secantCoefficientMap_globalDomain :
    Spec.map (CommRingCat.ofHom (secantCoefficientMap (S := S) W).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫
          integralCurveProductChart W false false =
      (Spec.map (CommRingCat.ofHom (secantRestriction V).toRingHom) ≫
        integralCurveProductChart V false false) ≫ integralCoefficientProduct W := by
  rw [Category.assoc, integralCoefficientProduct_affine]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ integralCurveProductChart W false false)
      (secantCoefficientMap_spec_restriction (S := S) W).symm).trans
        (Category.assoc _ _ _))

/-- An actual secant presentation computes the smooth sum without good reduction. -/
theorem smoothFactorAddition_secant {T : Scheme.{u}} (p : T ⟶ smoothFactorProduct W)
    (a : T ⟶ Spec (.of (SecantChart W)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫
      integralCurveProductChart W false false = p ≫ smoothFactorsInclusion W) :
    p ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι =
      a ≫ Spec.map (CommRingCat.ofHom (secantAddition W).toRingHom) ≫
        integralCurveChart W 2 :=
  smoothFactorAddition_chart W p .secant a ha

/-- The actual smooth addition is compatible even with bad-reduction coefficient changes. -/
@[reassoc] theorem originalSmoothCoefficientMap_addition :
    smoothFactorAddition V ≫ originalSmoothCoefficientMap S W =
      originalSmoothCoefficientProduct S W ≫ smoothFactorAddition W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  let _ : Flat (smoothFactorsInclusion V) := by
    rw [← smoothFactorsToProduct_inclusion]
    let _ : IsIso (smoothFactorsToProduct V) := (smoothProductFactorsIso V).symm.isIso_hom
    infer_instance
  apply flatProduct_hom_ext_secant V (smoothFactorsInclusion V) (integralCurveStructure W)
  · simp only [Category.assoc, originalSmoothCoefficientMap_inclusion]
    change smoothFactorAddition V ≫ (integralSmoothOpen V).ι ≫
        integralCoefficientMorphism W ≫ integralCurveStructure W =
      originalSmoothCoefficientProduct S W ≫
        smoothFactorAddition W ≫ integralSmoothStructure W
    rw [integralCoefficientMorphism_structure]
    change smoothFactorAddition V ≫ integralSmoothStructure V ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) = _
    rw [← Category.assoc, smoothFactorAddition_structure, Category.assoc,
      smoothFactorAddition_structure, originalSmoothCoefficientProduct_fst_assoc,
      originalSmoothCoefficientMap_structure]
  · intro U p a ha
    have hl := smoothFactorAddition_secant V p a ha
    have hr := smoothFactorAddition_secant W (p ≫ originalSmoothCoefficientProduct S W)
      (a ≫ Spec.map
        (CommRingCat.ofHom (secantCoefficientMap (S := S) W).toRingHom)) (by
          rw [Category.assoc, secantCoefficientMap_globalDomain, ← Category.assoc,
            ha]
          simp only [Category.assoc, originalSmoothCoefficientProduct_inclusion])
    simp only [Category.assoc, originalSmoothCoefficientMap_inclusion]
    rw [← Category.assoc (smoothFactorAddition V), ← Category.assoc p, hl, Category.assoc,
      Category.assoc, integralCurveChart_coefficientMorphism]
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
