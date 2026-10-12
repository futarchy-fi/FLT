/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbit
public import FLT.Mazur.WeierstrassDividedSmoothCoefficientUnique

/-!
# Smooth-output uniqueness in the complete sheared equation gluing

The actual coefficient and original-model legs reconstruct a smooth input
uniquely. This comparison applies to every test scheme.
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
  (S : Type) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "E" => coefficientShearGluedIso hπ data S r j hj
local notation "B" => coefficientShearSmoothEmbedding hπ data S r j hj
local notation "f" => coefficientShearGluedStructure hπ data S r j hj
local notation "p" => coefficientShearGluedProjection hπ data S r j hj

/-- Both actual reconstruction legs identify a sheared-model input with its smooth embedding. -/
theorem coefficientShear_eq_smoothEmbedding {T : Scheme}
    (s : T ⟶ (integralSmoothOpen V).toScheme)
    (g : T ⟶ coefficientShearGlued hπ data S r j hj)
    (hg : g ≫ f = s ≫ integralSmoothStructure V)
    (hc : g ≫ p ≫ finiteGlobalContraction hπ data j hj =
      s ≫ (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W) :
    g = s ≫ B := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearSmoothEmbedding_reconstruction]
  apply finiteGlobal_eq_smoothCoefficientEmbedding
  · simpa only [Category.assoc, coefficientShearGluedStructure] using hg
  · simpa only [Category.assoc, coefficientShearGluedProjection] using hc

/-- Equal structure and smooth contraction force equality in the full equation gluing. -/
theorem coefficientShear_smooth_hom_ext {T : Scheme}
    (s : T ⟶ (integralSmoothOpen V).toScheme)
    (g h : T ⟶ coefficientShearGlued hπ data S r j hj)
    (hg : g ≫ f = s ≫ integralSmoothStructure V)
    (hh : h ≫ f = s ≫ integralSmoothStructure V)
    (hgc : g ≫ p ≫ finiteGlobalContraction hπ data j hj =
      s ≫ (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W)
    (hhc : h ≫ p ≫ finiteGlobalContraction hπ data j hj =
      s ≫ (integralSmoothOpen V).ι ≫ integralCoefficientMorphism W) :
    g = h :=
  (coefficientShear_eq_smoothEmbedding hπ data S r j hj s g hg hgc).trans
    (coefficientShear_eq_smoothEmbedding hπ data S r j hj s h hh hhc).symm

end FLT.Mazur.WeierstrassDividedDepth
