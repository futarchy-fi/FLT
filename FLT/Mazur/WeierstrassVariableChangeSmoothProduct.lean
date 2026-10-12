/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVariableChangeSmoothIso
public import FLT.Mazur.WeierstrassVariableChangeProductMorphism
public import FLT.Mazur.WeierstrassSmoothFormulaComparison

/-!
# Variable changes on the actual product of smooth loci

The product comparison retains both original smooth inputs and the map
to the proper cubic product, even over a singular fiber.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)
local notation "e" => integralVariableChangeSmoothMap W V C h

/-- Apply the original variable change to both full smooth factors. -/
def integralVariableChangeSmoothProduct : smoothFactorProduct V ⟶ smoothFactorProduct W :=
  pullback.lift (pullback.fst _ _ ≫ e) (pullback.snd _ _ ≫ e) (by
    rw [Category.assoc, Category.assoc, integralVariableChangeSmoothMap_structure]
    exact pullback.condition)

/-- The first factor is the original smooth restriction of the proper variable change. -/
@[reassoc] theorem integralVariableChangeSmoothProduct_fst :
    integralVariableChangeSmoothProduct W V C h ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ e := pullback.lift_fst _ _ _

/-- The second factor retains the same original smooth restriction. -/
@[reassoc] theorem integralVariableChangeSmoothProduct_snd :
    integralVariableChangeSmoothProduct W V C h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ e := pullback.lift_snd _ _ _

/-- Both smooth inputs have exactly the proper cubic product comparison. -/
@[reassoc] theorem integralVariableChangeSmoothProduct_inclusion :
    integralVariableChangeSmoothProduct W V C h ≫ smoothFactorsInclusion W =
      smoothFactorsInclusion V ≫ integralVariableChangeProduct W V C h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, smoothFactorsInclusion_fst,
      integralVariableChangeSmoothProduct_fst_assoc, integralVariableChangeSmoothMap_inclusion,
      integralVariableChangeProduct_fst, smoothFactorsInclusion_fst_assoc]
  · simp only [Category.assoc, smoothFactorsInclusion_snd,
      integralVariableChangeSmoothProduct_snd_assoc, integralVariableChangeSmoothMap_inclusion,
      integralVariableChangeProduct_snd, smoothFactorsInclusion_snd_assoc]

end FLT.Mazur.WeierstrassIntegralChart
