/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSmoothCoefficientEmbedding
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothActionUnique

/-!
# Uniqueness of the coefficient smooth embedding

The coefficient structure and the original cubic contraction determine every
map above the original smooth locus, including maps from nonreduced schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "f" => finiteGlobalStructure hπ data j hj
local notation "E" => finiteGlobalSmoothCoefficientEmbedding S hπ data j hj

/-- Both pullback legs are fixed by the smooth coefficient input and its original contraction. -/
theorem finiteGlobal_eq_smoothCoefficientEmbedding {T : Scheme}
    (s : T ⟶ (integralSmoothOpen V).toScheme)
    (g : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (hg : g ≫ pullback.fst q f = s ≫ integralSmoothStructure V)
    (hc : g ≫ pullback.snd q f ≫ finiteGlobalContraction hπ data j hj =
      s ≫ (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W) :
    g = s ≫ E := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, finiteGlobalSmoothCoefficientEmbedding_structure] using hg
  · rw [Category.assoc, finiteGlobalSmoothCoefficientEmbedding_projection]
    rw [← Category.assoc s]
    apply finiteGlobal_eq_smoothEmbedding
    simpa only [Category.assoc, originalSmoothCoefficientMap_inclusion] using hc

/-- Smooth-output uniqueness after arbitrary coefficient extension requires both actual legs. -/
theorem finiteGlobal_smoothCoefficient_hom_ext {T : Scheme}
    (s : T ⟶ (integralSmoothOpen V).toScheme)
    (g h : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (hg : g ≫ pullback.fst q f = s ≫ integralSmoothStructure V)
    (hh : h ≫ pullback.fst q f = s ≫ integralSmoothStructure V)
    (hgc : g ≫ pullback.snd q f ≫ finiteGlobalContraction hπ data j hj =
      s ≫ (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W)
    (hhc : h ≫ pullback.snd q f ≫ finiteGlobalContraction hπ data j hj =
      s ≫ (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W) :
    g = h :=
  (finiteGlobal_eq_smoothCoefficientEmbedding hπ data S j hj s g hg hgc).trans
    (finiteGlobal_eq_smoothCoefficientEmbedding hπ data S j hj s h hh hhc).symm

end FLT.Mazur.WeierstrassDividedDepth
