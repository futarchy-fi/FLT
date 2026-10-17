/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedActionProduct
public import FLT.Mazur.PolygonCompleteClosedLaurentAction

/-!
# Closed Laurent action charts are actual products with the whole polygon

The zero-parameter family identifies with the full multiplicative-parameter
product. Under the original split component, it recovers the actual closed
input already used to compute the complete action.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "G" => PolygonSplitGroup.model K n
local notation "U" => MultiplicativeGroupScheme.gm K
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "q" => toBase K[T;T⁻¹] (LaurentPolynomial.C (0 : K)) n h
local notation "r" => scalingParameterProjection K 0 n h
local notation "z" => zeroFiberIso K n h

omit [NeZero n] in
/-- The unchanged Laurent family is the old multiplicative parameter times the whole polygon. -/
theorem completeClosedLaurentProduct_isPullback :
    IsPullback (q) ((r) ≫ (z).inv) (U).hom (C).hom := by
  apply (parameterProjection_isPullback (LaurentPolynomial.C : K →+* K[T;T⁻¹])
    0 (LaurentPolynomial.C 0) rfl n h).flip.of_iso'
      (Iso.refl _) (Iso.refl _) (z) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    exact zeroFiberIso_base K n h

/-- The entire original closed Laurent family is the actual old action chart product. -/
def completeClosedLaurentProductIso : scalingParameterFamily K 0 n h ≅ ((U) ⊗ (C)).left :=
  (completeClosedLaurentProduct_isPullback K n h).isoPullback

omit [NeZero n] in
/-- The first projection preserves the full independent Laurent parameter. -/
@[reassoc] theorem completeClosedLaurentProductIso_fst :
    (completeClosedLaurentProductIso K n h).hom ≫ (fst (U) (C)).left = (q) :=
  (completeClosedLaurentProduct_isPullback K n h).isoPullback_hom_fst

omit [NeZero n] in
/-- The second projection preserves the original whole polygon comparison. -/
@[reassoc] theorem completeClosedLaurentProductIso_snd :
    (completeClosedLaurentProductIso K n h).hom ≫ (snd (U) (C)).left = (r) ≫ (z).inv :=
  (completeClosedLaurentProduct_isPullback K n h).isoPullback_hom_snd

/-- The full split action input restricts to the already computed original closed chart. -/
@[reassoc] theorem completeClosedActionInput_laurent (i : Fin n) :
    (completeClosedLaurentProductIso K n h).hom ≫
        (PolygonSplitGroup.component K n (ZMod.finEquiv n i) ⊗ₘ 𝟙 (C)).left ≫
        completeClosedActionInput K n h = completeClosedLaurentInput K n h i := by
  have hf := congrArg Over.Hom.left
    (tensorHom_fst (PolygonSplitGroup.component K n (ZMod.finEquiv n i)) (𝟙 (C)))
  have hs := congrArg Over.Hom.left
    (tensorHom_snd (PolygonSplitGroup.component K n (ZMod.finEquiv n i)) (𝟙 (C)))
  simp only [Over.comp_left, Category.comp_id] at hf hs
  apply pullback.hom_ext
  · change _ ≫ (fst (M) (X)).left = _ ≫ (fst (M) (X)).left
    rw [Category.assoc, Category.assoc, completeClosedActionInput_fst,
      completeClosedLaurentInput_fst]
    rw [reassoc_of% hf, completeClosedLaurentProductIso_fst_assoc,
      component_completeClosedSplitInclusion]
  · change _ ≫ (snd (M) (X)).left = _ ≫ (snd (M) (X)).left
    rw [Category.assoc, Category.assoc, completeClosedActionInput_snd,
      completeClosedLaurentInput_snd]
    rw [reassoc_of% hs, completeClosedLaurentProductIso_snd_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
