/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothCoefficientAddition
public import FLT.Mazur.WeierstrassLeftSmoothPointAssociativity

/-!
# Smooth point sums commute with coefficient comparison

The scheme-level addition square gives the actual pointwise comparison
on every test scheme, without a flatness condition on the test points.
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

/-- Compatible smooth points remain compatible over the original coefficient spectrum. -/
theorem originalSmoothCoefficientPair_condition {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen V).toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ integralSmoothStructure V) :
    (a ≫ originalSmoothCoefficientMap S W) ≫ integralSmoothStructure W =
      (b ≫ originalSmoothCoefficientMap S W) ≫ integralSmoothStructure W := by
  simp only [Category.assoc, originalSmoothCoefficientMap_structure]
  exact congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) h

/-- Every actual smooth point sum is preserved by the original coefficient map. -/
@[reassoc] theorem originalSmoothCoefficientMap_pointAddition {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen V).toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ integralSmoothStructure V) :
    smoothPairPointAddition V a b h ≫ originalSmoothCoefficientMap S W =
      smoothPairPointAddition W (a ≫ originalSmoothCoefficientMap S W)
        (b ≫ originalSmoothCoefficientMap S W)
        (originalSmoothCoefficientPair_condition S W a b h) := by
  have hp : pullback.lift a b h ≫ originalSmoothCoefficientProduct S W =
      pullback.lift (a ≫ originalSmoothCoefficientMap S W)
        (b ≫ originalSmoothCoefficientMap S W)
        (originalSmoothCoefficientPair_condition S W a b h) := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, originalSmoothCoefficientProduct_fst,
        originalSmoothCoefficientProduct_snd, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  rw [smoothPairPointAddition, Category.assoc, originalSmoothCoefficientMap_addition,
    ← Category.assoc, hp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
