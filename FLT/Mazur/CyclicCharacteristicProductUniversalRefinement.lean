/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductRefinementAlgebra

/-!
# The full universal product comparisons satisfy concrete refinement

The affine universal overlap identity and the original-family transport
coherence give the refinement equation on the actual glued parameter cover.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
/-- An endpoint refinement square determines the inverse transport. -/
theorem iso_inverse_refinement {D : Type*} [Category* D] {A B X Y : D}
    (a : A ≅ X) (p : X ≅ Y) (l : A ≅ B) (b : B ≅ Y)
    (h : a ≪≫ p = l ≪≫ b) : p.symm ≪≫ a.symm ≪≫ l = b.symm := by
  calc
    _ = (a ≪≫ p).symm ≪≫ l := by
      apply Iso.ext
      simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
    _ = (l ≪≫ b).symm ≪≫ l := by rw [h]
    _ = _ := by simp

variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "C" => Scheme.Cover.RelativeGluingData.cover (productComparisonGluing n b c)
local notation "L" => productOpenLeft n b c
local notation "R" => productOpenRight n b c
variable {U V : (normalizedProduct n b c).affineOpens} (h : U ⟶ V)
local notation "m" => productOpenComparisonMap n b c (leOfHom h)
local notation "ap" => FiniteSubgroup.CompatibleIso.curve
  (productComparisonLeftRefinement n b c (U := U) (V := V) h)
local notation "dp" => FiniteSubgroup.CompatibleIso.curve
  (productComparisonRightRefinement n b c (U := U) (V := V) h)
local notation "aU" => productComparisonLeftChartIso n b c U
local notation "aV" => productComparisonLeftChartIso n b c V
local notation "dU" => productComparisonRightChartIso n b c U
local notation "dV" => productComparisonRightChartIso n b c V
local notation "cL" => coverRefinementIso C (productComparisonLeftCurve n b c) h
local notation "cR" => coverRefinementIso C (productComparisonRightCurve n b c) h

attribute [local irreducible] affineComparisonOverlapMap
  productComparisonLeftChartIso productComparisonRightChartIso
  productComparisonLeftRefinement productComparisonRightRefinement coverRefinementIso

/-- The inverse right transport satisfies the concrete refinement square. -/
theorem productComparisonRightChartIso_inverse_refine :
    (dp).symm ≪≫ (dU).symm ≪≫ cR = ((baseChangeFunctor m).mapIso dV).symm := by
  exact iso_inverse_refinement _ _ _ _ (productComparisonRightChartIso_refine n b c h)

/-- The refined large chart has its left transport in the smaller affine coordinates. -/
theorem productUniversalChartComparison_refine_left :
    cL ≪≫ (baseChangeFunctor m).mapIso (productUniversalChartComparison n b c V) =
      aU ≪≫ ap ≪≫
        (baseChangeFunctor m).mapIso (affineUniversalComparison n b c (L V) (R V)) ≪≫
          ((baseChangeFunctor m).mapIso dV).symm := by
  rw [productUniversalChartComparison_map n b c h]
  simp only [← Iso.trans_assoc]
  rw [← productComparisonLeftChartIso_refine n b c h]

/-- The smaller chart has the same expression after its right refinement. -/
theorem productUniversalChartComparison_refine_right :
    productUniversalChartComparison n b c U ≪≫ cR =
      aU ≪≫ ap ≪≫
        (baseChangeFunctor m).mapIso (affineUniversalComparison n b c (L V) (R V)) ≪≫
          ((baseChangeFunctor m).mapIso dV).symm := by
  unfold productUniversalChartComparison
  rw [productAffineUniversalComparison_refine n b c h]
  simp only [Iso.trans_assoc]
  rw [productComparisonRightChartIso_inverse_refine n b c h]

/-- The actual chart comparisons commute with the named affine overlap morphism. -/
theorem productUniversalChartComparison_refine_named :
    cL ≪≫ (baseChangeFunctor m).mapIso (productUniversalChartComparison n b c V) =
      productUniversalChartComparison n b c U ≪≫ cR :=
  (productUniversalChartComparison_refine_left n b c h).trans
    (productUniversalChartComparison_refine_right n b c h).symm

/-- The actual chart comparisons satisfy the full refinement identity needed for gluing. -/
theorem productUniversalChartComparison_refine :
    cL ≪≫ (baseChangeFunctor ((C).trans h)).mapIso (productUniversalChartComparison n b c V) =
      productUniversalChartComparison n b c U ≪≫ cR := by
  with_unfolding_all
    exact productUniversalChartComparison_refine_named n b c (U := U) (V := V) h

end FLT.Mazur.CyclicCharacteristicAtlas
