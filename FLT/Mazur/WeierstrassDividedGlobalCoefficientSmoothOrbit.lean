/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientActionLaws

/-!
# Intrinsic addition on the retained coefficient smooth orbit

The whole tensor-model action restricts to actual smooth addition over the
extended coefficient ring, on every test scheme and at every finite depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "emb" => finiteGlobalSmoothCoefficientEmbedding S hπ data j hj

/-- Translation on the retained smooth orbit is the intrinsic extended addition. -/
theorem finiteGlobalCoefficientPointAction_smoothEmbedding {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen V).toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ integralSmoothStructure V) :
    finiteGlobalCoefficientPointAction hπ data j hj S a (b ≫ emb)
        (by rw [Category.assoc, finiteGlobalSmoothCoefficientEmbedding_structure]; exact h) =
      smoothPairPointAddition V a b h ≫ emb := by
  apply pullback.hom_ext
  · rw [finiteGlobalCoefficientPointAction_structure, Category.assoc,
      finiteGlobalSmoothCoefficientEmbedding_structure, smoothPairPointAddition_structure]
  · simp only [finiteGlobalCoefficientPointAction_projection, Category.assoc,
      finiteGlobalSmoothCoefficientEmbedding_projection]
    simpa only [Category.assoc, originalSmoothCoefficientMap_pointAddition_assoc] using
      finiteGlobalPointAction_smoothEmbedding hπ data j hj
        (a ≫ originalSmoothCoefficientMap S W) (b ≫ originalSmoothCoefficientMap S W)
        (originalSmoothCoefficientPair_condition S W a b h)

/-- Arbitrary coefficient extension retains distinct smooth scheme-valued points. -/
theorem finiteGlobalSmoothCoefficientEmbedding_points_injective (T : Scheme.{u}) :
    Function.Injective (fun a : T ⟶ (integralSmoothOpen V).toScheme => a ≫ emb) := by
  intro a b h
  exact (cancel_mono emb).mp h

end FLT.Mazur.WeierstrassDividedDepth
