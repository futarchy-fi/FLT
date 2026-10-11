/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientBaseGroup

/-!
# The intrinsic smooth group commutes with arbitrary coefficient extension

The actual geometric comparison identifies the intrinsic extended group with
the categorical base change, including fibers of bad reduction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => integralSmoothStructure W

/-- The original smooth comparison as an isomorphism over the extended coefficient base. -/
def originalSmoothCoefficientOverIso :
    (integralSmoothGroup V).X ≅ (originalSmoothBaseChangeGroup S W).X :=
  Over.isoMk (originalSmoothCoefficientIso S W) (originalSmoothCoefficientIso_snd S W)

/-- Its product comparison is the actual map on the pair of smooth inputs. -/
theorem originalSmoothCoefficientOverIso_pair :
    ((originalSmoothCoefficientOverIso S W).hom ⊗ₘ
      (originalSmoothCoefficientOverIso S W).hom).left ≫
      pullback.lift (pullback.fst _ _ ≫ pullback.fst base q)
        (pullback.snd _ _ ≫ pullback.fst base q)
        (by simp only [Category.assoc, pullback.condition];
            exact congrArg (· ≫ q) pullback.condition) =
      originalSmoothCoefficientProduct S W := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc]
    erw [Over.tensorHom_left_fst]
    change (pullback.fst _ _ ≫ (originalSmoothCoefficientIso S W).hom) ≫ _ = _
    rw [Category.assoc, originalSmoothCoefficientIso_fst, originalSmoothCoefficientProduct_fst]
    rfl
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc]
    erw [Over.tensorHom_left_snd]
    change (pullback.snd _ _ ≫ (originalSmoothCoefficientIso S W).hom) ≫ _ = _
    rw [Category.assoc, originalSmoothCoefficientIso_fst, originalSmoothCoefficientProduct_snd]
    rfl

/-- The actual smooth coefficient isomorphism preserves the independently constructed groups. -/
def originalSmoothCoefficientGroupIso :
    integralSmoothGroup V ≅ originalSmoothBaseChangeGroup S W := by
  refine CommGrp.mkIso (originalSmoothCoefficientOverIso S W) ?_ ?_
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (integralSmoothZero V ≫ (originalSmoothCoefficientIso S W).hom) ≫
          pullback.fst base q = η[(originalSmoothBaseChangeGroup S W).X].left ≫
            pullback.fst base q
      rw [Category.assoc, originalSmoothCoefficientIso_fst,
        originalSmoothCoefficientMap_zero, originalSmoothBaseChangeGroup_one_fst]
    · exact (Over.w _).trans (Over.w _).symm
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (smoothFactorAddition V ≫ (originalSmoothCoefficientIso S W).hom) ≫
          pullback.fst base q =
        (((originalSmoothCoefficientOverIso S W).hom ⊗ₘ
          (originalSmoothCoefficientOverIso S W).hom).left ≫
          μ[(originalSmoothBaseChangeGroup S W).X].left) ≫ pullback.fst base q
      rw [Category.assoc, Category.assoc, originalSmoothCoefficientIso_fst,
        originalSmoothBaseChangeGroup_mul_fst, ← Category.assoc,
        originalSmoothCoefficientOverIso_pair, originalSmoothCoefficientMap_addition]
    · exact (Over.w _).trans (Over.w _).symm

/-- The group comparison retains the actual geometric coefficient isomorphism. -/
theorem originalSmoothCoefficientGroupIso_hom :
    (originalSmoothCoefficientGroupIso S W).hom.hom.hom.hom.left =
      (originalSmoothCoefficientIso S W).hom := rfl

end FLT.Mazur.WeierstrassDividedDepth
