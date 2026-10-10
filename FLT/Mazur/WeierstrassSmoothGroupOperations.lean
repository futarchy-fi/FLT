/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothTripleProduct
public import FLT.Mazur.WeierstrassSmoothAdditionIdentity
public import FLT.Mazur.WeierstrassSmoothAdditionInverse
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The smooth Weierstrass operations in the category over the base

The actual addition, infinity section and negation define morphisms over the
coefficient spectrum. Their product constraints recover the fiber-product
maps used in the global group-law proofs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The full relative smooth curve as a scheme over its coefficient spectrum. -/
abbrev integralSmoothOver : Over (Spec (.of R)) := Over.mk (integralSmoothStructure W)

/-- Infinity as a morphism from the monoidal unit over the base. -/
def integralSmoothOverZero : 𝟙_ (Over (Spec (.of R))) ⟶ integralSmoothOver W :=
  Over.homMk (integralSmoothZero W) (integralSmoothZero_structure W)

/-- The global negation is a morphism over the base. -/
def integralSmoothOverNegation : integralSmoothOver W ⟶ integralSmoothOver W :=
  Over.homMk (integralSmoothNegation W) (integralSmoothNegation_structure W)

/-- The constructed global addition is a morphism in the slice category. -/
def integralSmoothOverAddition :
    integralSmoothOver W ⊗ integralSmoothOver W ⟶ integralSmoothOver W :=
  Over.homMk (smoothFactorAddition W) (smoothFactorAddition_structure W)

/-- The left unit constraint gives the original zero pairing. -/
theorem integralSmoothOver_leftZero :
    (λ_ (integralSmoothOver W)).inv.left ≫
      (integralSmoothOverZero W ▷ integralSmoothOver W).left = smoothFactorLeftZero W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerRight_left_fst, ← Category.assoc]
    exact (congrArg (fun f => f ≫ (integralSmoothOverZero W).left)
      (Over.leftUnitor_inv_left_fst _)).trans (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, Over.whiskerRight_left_snd]
    exact (Over.leftUnitor_inv_left_snd _).trans (pullback.lift_snd _ _ _).symm

/-- The right unit constraint gives the original opposite zero pairing. -/
theorem integralSmoothOver_rightZero :
    (ρ_ (integralSmoothOver W)).inv.left ≫
      (integralSmoothOver W ◁ integralSmoothOverZero W).left = smoothFactorRightZero W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerLeft_left_fst]
    exact (Over.rightUnitor_inv_left_fst _).trans (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, Over.whiskerLeft_left_snd, ← Category.assoc]
    exact (congrArg (fun f => f ≫ (integralSmoothOverZero W).left)
      (Over.rightUnitor_inv_left_snd _)).trans (pullback.lift_snd _ _ _).symm

/-- The left-associated categorical pair is the existing actual pair. -/
theorem integralSmoothOver_addFirst :
    (integralSmoothOverAddition W ▷ integralSmoothOver W).left =
      smoothFactorAddFirstPair W := by
  apply pullback.hom_ext
  · exact (Over.whiskerRight_left_fst _).trans (smoothFactorAddFirstPair_fst W).symm
  · exact (Over.whiskerRight_left_snd _).trans (smoothFactorAddFirstPair_snd W).symm

/-- The associator followed by the last pair is the existing actual last pair. -/
theorem integralSmoothOver_lastPair :
    (α_ (integralSmoothOver W) (integralSmoothOver W) (integralSmoothOver W)).hom.left ≫
      pullback.snd _ _ = smoothFactorTripleLastPair W := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    exact (Over.associator_hom_left_snd_fst _ _ _).trans
      (smoothFactorTripleLastPair_fst W).symm
  · rw [Category.assoc]
    exact (Over.associator_hom_left_snd_snd _ _ _).trans
      (smoothFactorTripleLastPair_snd W).symm

/-- The right-associated categorical pair is the existing actual pair. -/
theorem integralSmoothOver_addLast :
    (α_ (integralSmoothOver W) (integralSmoothOver W) (integralSmoothOver W)).hom.left ≫
      (integralSmoothOver W ◁ integralSmoothOverAddition W).left =
        smoothFactorAddLastPair W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerLeft_left_fst]
    exact (Over.associator_hom_left_fst _ _ _).trans
      (smoothFactorAddLastPair_fst W).symm
  · rw [Category.assoc, Over.whiskerLeft_left_snd, ← Category.assoc]
    exact (congrArg (fun f => f ≫ smoothFactorAddition W)
      (integralSmoothOver_lastPair W)).trans (smoothFactorAddLastPair_snd W).symm

end FLT.Mazur.WeierstrassIntegralChart
