/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbitDescent

/-!
# Recover the retained smooth orbit from the original cubic map

The actual coefficient structure and cubic contraction determine maps from
the original smooth scheme uniquely. Its entire image is the full inverse
image of the original smooth open under that contraction.
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
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "p" => coefficientShearGluedProjection hπ data S r j hj
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "B" => coefficientShearSmoothEmbedding hπ data S r j hj
local notation "U" => originalSmoothCoefficientMap S W

/-- The entire retained smooth orbit contracts by the original coefficient cubic map. -/
@[reassoc] theorem coefficientShearSmoothEmbedding_contraction :
    B ≫ p ≫ c = (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W := by
  rw [coefficientShearSmoothEmbedding_projection_assoc,
    finiteGlobalSmoothEmbedding_contraction, originalSmoothCoefficientMap_inclusion]

/-- The complete smooth orbit is exactly the inverse image of the original smooth cubic open. -/
theorem coefficientShearSmoothEmbedding_contraction_range :
    Set.range B = (p ≫ c) ⁻¹' (integralSmoothOpen W : Set _) := by
  rw [coefficientShearSmoothEmbedding_range, finiteGlobalSmoothEmbedding_range]
  rfl

/-- Actual structure and cubic maps uniquely recover a morphism into the retained smooth orbit. -/
theorem coefficientShearSmoothEmbedding_recover {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ coefficientShearGlued hπ data S r j hj)
    (hb : b ≫ g = a ≫ integralSmoothStructure V)
    (hc : b ≫ p ≫ c = a ≫ (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W) :
    b = a ≫ B := by
  have hw : (a ≫ U) ≫ (integralSmoothOpen W).ι = (b ≫ p) ≫ c := by
    rw [Category.assoc, originalSmoothCoefficientMap_inclusion, Category.assoc]
    exact hc.symm
  let H := finiteGlobalSmoothEmbedding_isPullback hπ data j hj
  have hl : H.lift (a ≫ U) (b ≫ p) hw = a ≫ U := by
    simpa only [Category.comp_id] using H.lift_fst (a ≫ U) (b ≫ p) hw
  have hp := H.lift_snd (a ≫ U) (b ≫ p) hw
  rw [hl] at hp
  apply (coefficientShearGlued_isPullback hπ data S r j hj).hom_ext
  · rw [Category.assoc, coefficientShearSmoothEmbedding_structure]
    exact hb
  · rw [Category.assoc, coefficientShearSmoothEmbedding_projection]
    exact hp.symm.trans (Category.assoc _ _ _)

end FLT.Mazur.WeierstrassDividedDepth
