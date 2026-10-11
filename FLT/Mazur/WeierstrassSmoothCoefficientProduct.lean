/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientOperations
public import FLT.Mazur.WeierstrassCoefficientProductMorphism
public import FLT.Mazur.WeierstrassSmoothFormulaComparison

/-!
# The actual coefficient map on pairs of smooth points

The smooth coefficient map induces a map on the actual categorical product.
Its inclusion is the original coefficient map on the entire cubic product.
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

/-- Apply the actual smooth coefficient map to both inputs. -/
def originalSmoothCoefficientProduct : smoothFactorProduct V ⟶ smoothFactorProduct W :=
  pullback.lift (pullback.fst _ _ ≫ originalSmoothCoefficientMap S W)
    (pullback.snd _ _ ≫ originalSmoothCoefficientMap S W) (by
      rw [Category.assoc, Category.assoc, originalSmoothCoefficientMap_structure]
      exact congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (pullback.condition (f := integralSmoothStructure V) (g := integralSmoothStructure V)))

/-- The first smooth input is the original coefficient comparison. -/
@[reassoc] theorem originalSmoothCoefficientProduct_fst :
    originalSmoothCoefficientProduct S W ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ originalSmoothCoefficientMap S W := pullback.lift_fst _ _ _

/-- The second smooth input is the original coefficient comparison. -/
@[reassoc] theorem originalSmoothCoefficientProduct_snd :
    originalSmoothCoefficientProduct S W ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ originalSmoothCoefficientMap S W := pullback.lift_snd _ _ _

/-- Including the smooth pair recovers the original whole coefficient product. -/
@[reassoc] theorem originalSmoothCoefficientProduct_inclusion :
    originalSmoothCoefficientProduct S W ≫ smoothFactorsInclusion W =
      smoothFactorsInclusion V ≫ integralCoefficientProduct W := by
  apply pullback.hom_ext
  · simp only [Category.assoc, smoothFactorsInclusion_fst,
      originalSmoothCoefficientProduct_fst_assoc, originalSmoothCoefficientMap_inclusion,
      integralCoefficientProduct_fst, smoothFactorsInclusion_fst_assoc]
  · simp only [Category.assoc, smoothFactorsInclusion_snd,
      originalSmoothCoefficientProduct_snd_assoc, originalSmoothCoefficientMap_inclusion,
      integralCoefficientProduct_snd, smoothFactorsInclusion_snd_assoc]

end FLT.Mazur.WeierstrassDividedDepth
