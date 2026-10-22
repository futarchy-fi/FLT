/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeSmoothAddition
public import FLT.Mazur.WeierstrassVariableChangeZero
public import FLT.Mazur.WeierstrassSmoothGroup

/-!
# Admissible changes preserve the intrinsic group on singular fibers

The actual restriction of the proper cubic change preserves the independently
constructed identity and multiplication on the entire smooth open. No unit
condition on the discriminant is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

/-- The smooth restriction retains the original identity section. -/
@[reassoc] theorem integralVariableChangeSmoothMap_zero :
    integralSmoothZero V ≫ integralVariableChangeSmoothMap W V C h =
      integralSmoothZero W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [Category.assoc, integralVariableChangeSmoothMap_inclusion,
    integralSmoothZero_inclusion_assoc, integralSmoothZero_inclusion,
    integralVariableChangeIso_zero]

/-- The categorical pair of smooth comparisons is the original product map. -/
theorem integralVariableChangeSmoothOverIso_tensor :
    ((integralVariableChangeSmoothOverIso W V C h).hom ⊗ₘ
      (integralVariableChangeSmoothOverIso W V C h).hom).left =
        integralVariableChangeSmoothProduct W V C h := by
  apply pullback.hom_ext
  · exact (Over.tensorHom_left_fst _ _ _ _).trans
      (integralVariableChangeSmoothProduct_fst W V C h).symm
  · exact (Over.tensorHom_left_snd _ _ _ _).trans
      (integralVariableChangeSmoothProduct_snd W V C h).symm

/-- The original smooth comparison is a group isomorphism even on nodal fibers. -/
def integralVariableChangeIntrinsicGroupIso : integralSmoothGroup V ≅ integralSmoothGroup W := by
  refine CommGrp.mkIso (integralVariableChangeSmoothOverIso W V C h) ?_ ?_
  · apply Over.OverMorphism.ext
    exact integralVariableChangeSmoothMap_zero W V C h
  · apply Over.OverMorphism.ext
    change smoothFactorAddition V ≫ integralVariableChangeSmoothMap W V C h =
      ((integralVariableChangeSmoothOverIso W V C h).hom ⊗ₘ
        (integralVariableChangeSmoothOverIso W V C h).hom).left ≫ smoothFactorAddition W
    rw [integralVariableChangeSmoothOverIso_tensor]
    exact integralVariableChangeSmoothMap_addition W V C h

/-- Forgetting the intrinsic group comparison recovers the exact smooth restriction. -/
theorem integralVariableChangeIntrinsicGroupIso_hom :
    (integralVariableChangeIntrinsicGroupIso W V C h).hom.hom.hom.hom.left =
      integralVariableChangeSmoothMap W V C h := rfl

/-- The group isomorphism and proper comparison retain the original smooth inclusion. -/
@[reassoc] theorem integralVariableChangeIntrinsicGroupIso_inclusion :
    (integralVariableChangeIntrinsicGroupIso W V C h).hom.hom.hom.hom.left ≫
      (integralSmoothOpen W).ι =
        (integralSmoothOpen V).ι ≫ (integralVariableChangeIso W V C h).hom :=
  integralVariableChangeSmoothMap_inclusion W V C h

end FLT.Mazur.WeierstrassIntegralChart
