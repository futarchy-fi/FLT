/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralTripleProduct
public import FLT.Mazur.WeierstrassNegationPairSections
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The integral Weierstrass operations in the category over the base

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

/-- The glued integral cubic as a scheme over its coefficient spectrum. -/
abbrev integralCurveOver : Over (Spec (.of R)) := Over.mk (integralCurveStructure W)

/-- Infinity as a morphism from the monoidal unit over the base. -/
def integralCurveOverZero : 𝟙_ (Over (Spec (.of R))) ⟶ integralCurveOver W :=
  Over.homMk (integralCurveZero W) (integralCurveZero_structure W)

/-- The global negation is a morphism over the base. -/
def integralCurveOverNegation : integralCurveOver W ⟶ integralCurveOver W :=
  Over.homMk (integralCurveNegation W) (integralCurveNegation_structure W)

/-- The constructed global addition is a morphism in the slice category. -/
def integralCurveOverAddition (hΔ : IsUnit W.Δ) :
    integralCurveOver W ⊗ integralCurveOver W ⟶ integralCurveOver W :=
  Over.homMk (integralCurveAddition W hΔ) (integralCurveAddition_structure W hΔ)

/-- The left unit constraint gives the original zero pairing. -/
theorem integralCurveOver_leftZero :
    (λ_ (integralCurveOver W)).inv.left ≫
      (integralCurveOverZero W ▷ integralCurveOver W).left = integralCurveLeftZero W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerRight_left_fst, ← Category.assoc]
    exact (congrArg (fun f => f ≫ (integralCurveOverZero W).left)
      (Over.leftUnitor_inv_left_fst _)).trans (integralCurveLeftZero_fst W).symm
  · rw [Category.assoc, Over.whiskerRight_left_snd]
    exact (Over.leftUnitor_inv_left_snd _).trans (integralCurveLeftZero_snd W).symm

/-- The right unit constraint gives the original opposite zero pairing. -/
theorem integralCurveOver_rightZero :
    (ρ_ (integralCurveOver W)).inv.left ≫
      (integralCurveOver W ◁ integralCurveOverZero W).left = integralCurveRightZero W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerLeft_left_fst]
    exact (Over.rightUnitor_inv_left_fst _).trans (integralCurveRightZero_fst W).symm
  · rw [Category.assoc, Over.whiskerLeft_left_snd, ← Category.assoc]
    exact (congrArg (fun f => f ≫ (integralCurveOverZero W).left)
      (Over.rightUnitor_inv_left_snd _)).trans (integralCurveRightZero_snd W).symm

/-- The left-associated categorical pair is the existing actual pair. -/
theorem integralCurveOver_addFirst (hΔ : IsUnit W.Δ) :
    (integralCurveOverAddition W hΔ ▷ integralCurveOver W).left =
      integralCurveAddFirstPair W hΔ := by
  apply pullback.hom_ext
  · exact (Over.whiskerRight_left_fst _).trans (integralCurveAddFirstPair_fst W hΔ).symm
  · exact (Over.whiskerRight_left_snd _).trans (integralCurveAddFirstPair_snd W hΔ).symm

/-- The associator followed by the last pair is the existing actual last pair. -/
theorem integralCurveOver_lastPair :
    (α_ (integralCurveOver W) (integralCurveOver W) (integralCurveOver W)).hom.left ≫
      pullback.snd _ _ = integralCurveTripleLastPair W := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    exact (Over.associator_hom_left_snd_fst _ _ _).trans
      (integralCurveTripleLastPair_fst W).symm
  · rw [Category.assoc]
    exact (Over.associator_hom_left_snd_snd _ _ _).trans
      (integralCurveTripleLastPair_snd W).symm

/-- The right-associated categorical pair is the existing actual pair. -/
theorem integralCurveOver_addLast (hΔ : IsUnit W.Δ) :
    (α_ (integralCurveOver W) (integralCurveOver W) (integralCurveOver W)).hom.left ≫
      (integralCurveOver W ◁ integralCurveOverAddition W hΔ).left =
        integralCurveAddLastPair W hΔ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerLeft_left_fst]
    exact (Over.associator_hom_left_fst _ _ _).trans
      (integralCurveAddLastPair_fst W hΔ).symm
  · rw [Category.assoc, Over.whiskerLeft_left_snd, ← Category.assoc]
    exact (congrArg (fun f => f ≫ integralCurveAddition W hΔ)
      (integralCurveOver_lastPair W)).trans (integralCurveAddLastPair_snd W hΔ).symm

end FLT.Mazur.WeierstrassIntegralChart
