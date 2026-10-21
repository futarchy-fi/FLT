/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientProduct
public import FLT.Mazur.WeierstrassLeftSmoothFactorProduct

/-!
# Coefficient change on the full smooth-by-whole action domain

The first input changes by the intrinsic smooth coefficient map. The second
retains the whole cubic, including its singular points. The resulting map
commutes with the inclusion into the full cubic product.
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

/-- Change coefficients of a smooth input and an unrestricted original cubic input. -/
def originalLeftSmoothCoefficientProduct :
    leftSmoothFactorProduct V ⟶ leftSmoothFactorProduct W :=
  pullback.lift (pullback.fst _ _ ≫ originalSmoothCoefficientMap S W)
    (pullback.snd _ _ ≫ integralCoefficientMorphism W) (by
      rw [Category.assoc, Category.assoc, originalSmoothCoefficientMap_structure,
        integralCoefficientMorphism_structure]
      exact congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (pullback.condition (f := integralSmoothStructure V) (g := integralCurveStructure V)))

/-- The smooth input retains its actual coefficient projection. -/
@[reassoc] theorem originalLeftSmoothCoefficientProduct_fst :
    originalLeftSmoothCoefficientProduct S W ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ originalSmoothCoefficientMap S W := pullback.lift_fst _ _ _

/-- The unrestricted input retains its entire cubic coefficient projection. -/
@[reassoc] theorem originalLeftSmoothCoefficientProduct_snd :
    originalLeftSmoothCoefficientProduct S W ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ integralCoefficientMorphism W := pullback.lift_snd _ _ _

/-- The map is exactly the original coefficient product on the full action domain. -/
@[reassoc] theorem originalLeftSmoothCoefficientProduct_inclusion :
    originalLeftSmoothCoefficientProduct S W ≫ leftSmoothFactorsInclusion W =
      leftSmoothFactorsInclusion V ≫ integralCoefficientProduct W := by
  apply pullback.hom_ext
  · simp only [Category.assoc, leftSmoothFactorsInclusion, pullback.lift_fst,
      originalLeftSmoothCoefficientProduct_fst_assoc, originalSmoothCoefficientMap_inclusion,
      integralCoefficientProduct_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, leftSmoothFactorsInclusion, pullback.lift_snd,
      originalLeftSmoothCoefficientProduct_snd, integralCoefficientProduct_snd,
      pullback.lift_snd_assoc]

end FLT.Mazur.WeierstrassDividedDepth
