/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAssociativity

/-!
# Scheme-valued associativity for the integral action

Pulling back the proved triple-product identity gives associativity for arbitrary
scheme-valued original inputs, with their specified common coefficient map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual sum of two compatible smooth scheme-valued points. -/
def smoothPairPointAddition {X : Scheme.{u}}
    (a b : X ⟶ (integralSmoothOpen W).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W) :
    X ⟶ (integralSmoothOpen W).toScheme :=
  pullback.lift a b h ≫ smoothFactorAddition W

/-- The smooth point sum retains its original coefficient morphism. -/
@[reassoc] theorem smoothPairPointAddition_structure {X : Scheme.{u}}
    (a b : X ⟶ (integralSmoothOpen W).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W) :
    smoothPairPointAddition W a b h ≫ integralSmoothStructure W =
      a ≫ integralSmoothStructure W := by
  rw [smoothPairPointAddition, Category.assoc, smoothFactorAddition_structure,
    pullback.lift_fst_assoc]

/-- The original smooth point sum acts as the composition of the two original actions. -/
theorem leftSmoothPointAddition_assoc {X : Scheme.{u}}
    (a b : X ⟶ (integralSmoothOpen W).toScheme) (c : X ⟶ integralCurve W)
    (hab : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W)
    (hbc : b ≫ integralSmoothStructure W = c ≫ integralCurveStructure W) :
    leftSmoothPointAddition W (smoothPairPointAddition W a b hab) c
        (by rw [smoothPairPointAddition_structure]; exact hab.trans hbc) =
      leftSmoothPointAddition W a (leftSmoothPointAddition W b c hbc)
        (by rw [leftSmoothPointAddition_structure]; exact hab) := by
  let t : X ⟶ leftSmoothTriple W :=
    pullback.lift (pullback.lift a b hab) c (by
      change (pullback.lift a b hab) ≫ pullback.fst _ _ ≫ integralSmoothStructure W = _
      rw [pullback.lift_fst_assoc]
      exact hab.trans hbc)
  have ht : t ≫ leftSmoothTriplePair W = pullback.lift a b hab :=
    pullback.lift_fst _ _ _
  have h₁ : t ≫ leftSmoothTripleFirst W = a := by
    rw [leftSmoothTripleFirst, ← Category.assoc, ht, pullback.lift_fst]
  have h₂ : t ≫ leftSmoothTripleSecond W = b := by
    rw [leftSmoothTripleSecond, ← Category.assoc, ht, pullback.lift_snd]
  have h₃ : t ≫ leftSmoothTripleThird W = c := pullback.lift_snd _ _ _
  have hlast : t ≫ leftSmoothTripleLastPair W = pullback.lift b c hbc := by
    apply pullback.hom_ext
    · rw [Category.assoc, leftSmoothTripleLastPair_fst, h₂, pullback.lift_fst]
    · rw [Category.assoc, leftSmoothTripleLastPair_snd, h₃, pullback.lift_snd]
  have hl : t ≫ leftSmoothAddFirstPair W =
      pullback.lift (smoothPairPointAddition W a b hab) c
        (by rw [smoothPairPointAddition_structure]; exact hab.trans hbc) := by
    apply pullback.hom_ext
    · rw [Category.assoc, leftSmoothAddFirstPair_fst, ← Category.assoc, ht,
        pullback.lift_fst]
      rfl
    · rw [Category.assoc, leftSmoothAddFirstPair_snd, h₃, pullback.lift_snd]
  have hr : t ≫ leftSmoothAddLastPair W =
      pullback.lift a (leftSmoothPointAddition W b c hbc)
        (by rw [leftSmoothPointAddition_structure]; exact hab) := by
    apply pullback.hom_ext
    · rw [Category.assoc, leftSmoothAddLastPair_fst, h₁, pullback.lift_fst]
    · rw [Category.assoc, leftSmoothAddLastPair_snd, ← Category.assoc, hlast,
        pullback.lift_snd]
      rfl
  have he := congrArg (fun f => t ≫ f) (leftSmoothFactorAddition_assoc W)
  simpa only [leftSmoothTripleAddLeft, leftSmoothTripleAddRight, ← Category.assoc,
    hl, hr, leftSmoothPointAddition] using he

end FLT.Mazur.WeierstrassIntegralChart
