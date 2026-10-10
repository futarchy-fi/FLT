/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientAffineProduct
public import FLT.Mazur.WeierstrassIntegralCoefficientMap
public import FLT.Mazur.WeierstrassIntegralCurveProduct

/-!
# The actual proper input product under coefficient extension

The global coefficient map acts on both inputs over the coefficient spectrum.
Its restriction is exactly the original affine product coefficient map.
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

/-- Apply coefficient extension to both inputs of the original fiber product. -/
def integralCoefficientProduct : integralCurveProduct V ⟶ integralCurveProduct W :=
  pullback.lift
    (pullback.fst _ _ ≫ integralCoefficientMorphism (S := S) W)
    (pullback.snd _ _ ≫ integralCoefficientMorphism (S := S) W) (by
      simp only [Category.assoc, integralCoefficientMorphism_structure, pullback.condition_assoc])

/-- The first projection retains the actual coefficient morphism. -/
@[reassoc] theorem integralCoefficientProduct_fst :
    integralCoefficientProduct (S := S) W ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ integralCoefficientMorphism (S := S) W := pullback.lift_fst ..

/-- The second projection retains the same coefficient morphism. -/
@[reassoc] theorem integralCoefficientProduct_snd :
    integralCoefficientProduct (S := S) W ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ integralCoefficientMorphism (S := S) W := pullback.lift_snd ..

/-- The affine product map retains the first actual affine coefficient map. -/
theorem affineProductCoefficientMap_spec_left :
    Spec.map (CommRingCat.ofHom (affineProductCoefficientMap (S := S) W).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (productLeft W).toRingHom) =
      Spec.map (CommRingCat.ofHom (productLeft V).toRingHom) ≫
        chartCoefficientMorphism (S := S) W 2 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (affineProductCoefficientMap_left (S := S) W)

/-- The affine product map retains the second actual affine coefficient map. -/
theorem affineProductCoefficientMap_spec_right :
    Spec.map (CommRingCat.ofHom (affineProductCoefficientMap (S := S) W).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (productRight W).toRingHom) =
      Spec.map (CommRingCat.ofHom (productRight V).toRingHom) ≫
        chartCoefficientMorphism (S := S) W 2 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (affineProductCoefficientMap_right (S := S) W)

/-- The full product morphism restricts to the original affine coefficient map on both inputs. -/
@[reassoc] theorem integralCoefficientProduct_affine :
    integralCurveProductChart V false false ≫ integralCoefficientProduct (S := S) W =
      Spec.map (CommRingCat.ofHom (affineProductCoefficientMap (S := S) W).toRingHom) ≫
        integralCurveProductChart W false false := by
  apply pullback.hom_ext
  · simp only [Category.assoc, integralCoefficientProduct_fst,
      integralCurveProductChart_fst]
    rw [← Category.assoc, integralCurveProductChart_fst, Category.assoc]
    change Spec.map (CommRingCat.ofHom (productLeft V).toRingHom) ≫
      integralCurveChart V 2 ≫ integralCoefficientMorphism (S := S) W = _
    rw [integralCurveChart_coefficientMorphism, ← Category.assoc]
    exact congrArg (· ≫ integralCurveChart W 2)
      (affineProductCoefficientMap_spec_left (S := S) W).symm
  · simp only [Category.assoc, integralCoefficientProduct_snd,
      integralCurveProductChart_snd]
    rw [← Category.assoc, integralCurveProductChart_snd, Category.assoc]
    change Spec.map (CommRingCat.ofHom (productRight V).toRingHom) ≫
      integralCurveChart V 2 ≫ integralCoefficientMorphism (S := S) W = _
    rw [integralCurveChart_coefficientMorphism, ← Category.assoc]
    exact congrArg (· ≫ integralCurveChart W 2)
      (affineProductCoefficientMap_spec_right (S := S) W).symm

end FLT.Mazur.WeierstrassIntegralChart
