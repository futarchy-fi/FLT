/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedOrientedAtlas
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor

/-!
# Natural retained labels and the original finite-stage arithmetic charts

The positive label j and negative label depth-j retain their full arithmetic
maps. Their target transport is only equality of the original finite stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)

/-- The named finite-stage isomorphism is precisely transport along equality of the stages. -/
theorem finiteTensorIndexIso_hom_eqToHom
    {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
    (data : (i : Fin (n + 1)) → Data W π (start + i.val))
    (S : Type u) [CommRing S] [Algebra A S]
    (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (he : i = j) :
    (finiteTensorIndexIso A hπ data S i j hi hj he).hom =
      eqToHom (finiteGlobalTensorModel_index_congr hπ data S hi hj he) := by
  subst j
  rfl

variable {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2)
local notation "F" => ResidueField A
local notation "p" => resolvedSplitStructure A D
local notation "e" => resolvedComponentIndexEquiv D.depth_pos
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "data" => splitResolutionData A D

/-- Natural label j includes as its original positive retained arithmetic chart. -/
@[reassoc] theorem resolvedOrientedComponentChart_retainedPositive :
    resolvedOrientedComponentChart A D r ⟨j, by omega⟩ ≫ (p).smoothLocus.ι =
      resolvedRetainedPositiveChart A D r j hj0 hj := by
  have hi : (e) (.retainedPositive j hj0 hj) = ⟨j, by omega⟩ := rfl
  rw [← hi, resolvedOrientedComponentChart, Equiv.symm_apply_apply]
  simp only [resolvedComponentOrientation, reduceCtorEq, ite_false, Iso.refl_hom,
    Category.id_comp, resolvedComponentChart, resolvedRetainedPositiveSmoothChart_inclusion]

/-- The complementary label depth-j includes as the original negative arithmetic chart. -/
@[reassoc] theorem resolvedOrientedComponentChart_retainedNegative :
    resolvedOrientedComponentChart A D r ⟨depth - j, by omega⟩ ≫ (p).smoothLocus.ι =
      resolvedRetainedNegativeChart A D r j hj0 hj := by
  have hi : (e) (.retainedNegative j hj0 hj) = ⟨depth - j, by omega⟩ := rfl
  rw [← hi, resolvedOrientedComponentChart, Equiv.symm_apply_apply]
  simp only [resolvedComponentOrientation, reduceCtorEq, ite_false, Iso.refl_hom,
    Category.id_comp, resolvedComponentChart, resolvedRetainedNegativeSmoothChart_inclusion]

variable (m : ℕ) (hm : j + 1 + m = depth / 2)

/-- A chosen retention length preserves the entire original positive arithmetic map. -/
theorem resolvedRetainedPositiveChart_original_heq :
    HEq (resolvedRetainedPositiveChart A D r j hj0 hj)
      (retainedTrivializedPositiveChart A hπ data D r j (by omega) m (by omega)
        (by omega) (by omega)) := by
  rw [resolvedRetainedPositiveChart, finiteTensorIndexIso_hom_eqToHom]
  refine (comp_eqToHom_heq _ _).trans ?_
  have he : depth / 2 - (j + 1) = m := by omega
  subst m
  rfl

/-- A chosen retention length preserves the entire original negative arithmetic map. -/
theorem resolvedRetainedNegativeChart_original_heq :
    HEq (resolvedRetainedNegativeChart A D r j hj0 hj)
      (retainedTrivializedNegativeChart A hπ data D r j (by omega) m (by omega)
        (by omega) (by omega)) := by
  rw [resolvedRetainedNegativeChart, finiteTensorIndexIso_hom_eqToHom]
  refine (comp_eqToHom_heq _ _).trans ?_
  have he : depth / 2 - (j + 1) = m := by omega
  subst m
  rfl

end FLT.Mazur.WeierstrassDividedDepth
