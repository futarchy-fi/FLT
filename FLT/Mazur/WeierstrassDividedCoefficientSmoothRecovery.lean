/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSmoothCoefficientEmbedding

/-!
# Recover the independent coefficient smooth embedding from its original maps

The coefficient structure and integral cubic contraction uniquely determine
maps into the retained full smooth orbit in the original tensor model.
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
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "g" => finiteGlobalStructure hπ data j hj
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "B" => finiteGlobalSmoothCoefficientEmbedding S hπ data j hj
local notation "U" => originalSmoothCoefficientMap S W

/-- The actual two original maps uniquely recover the full retained smooth embedding. -/
theorem finiteGlobalSmoothCoefficientEmbedding_recover {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (hb : b ≫ pullback.fst q g = a ≫ integralSmoothStructure V)
    (hc : b ≫ pullback.snd q g ≫ c =
      a ≫ (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W) : b = a ≫ B := by
  have hw : (a ≫ U) ≫ (integralSmoothOpen W).ι = (b ≫ pullback.snd q g) ≫ c := by
    rw [Category.assoc, originalSmoothCoefficientMap_inclusion, Category.assoc]
    exact hc.symm
  let H := finiteGlobalSmoothEmbedding_isPullback hπ data j hj
  have hl : H.lift (a ≫ U) (b ≫ pullback.snd q g) hw = a ≫ U := by
    simpa only [Category.comp_id] using H.lift_fst (a ≫ U) (b ≫ pullback.snd q g) hw
  have hp := H.lift_snd (a ≫ U) (b ≫ pullback.snd q g) hw
  rw [hl] at hp
  apply pullback.hom_ext
  · rw [Category.assoc, finiteGlobalSmoothCoefficientEmbedding_structure]
    exact hb
  · rw [Category.assoc, finiteGlobalSmoothCoefficientEmbedding_projection]
    exact hp.symm.trans (Category.assoc _ _ _)

end FLT.Mazur.WeierstrassDividedDepth
