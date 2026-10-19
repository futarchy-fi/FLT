/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductRefinementTransport

/-!
# Algebra for full universal product refinement

The actual affine overlap retains the full comparison. Abstract conjugation
identities and the chart pullback formula prepare its transport to the global families.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
/-- Commuting endpoint squares transport a conjugated comparison through refinement. -/
theorem iso_conjugate_refinement {D : Type*} [Category* D]
    {A B A' B' X Y X' Y' : D}
    (a : A ≅ X) (b : B ≅ Y) (a' : A' ≅ X') (b' : B' ≅ Y')
    (l : A ≅ A') (r : B ≅ B') (p : X ≅ X') (q : Y ≅ Y')
    (e : X ≅ Y) (e' : X' ≅ Y')
    (ha : a ≪≫ p = l ≪≫ a') (hb : b ≪≫ q = r ≪≫ b')
    (he : e = p ≪≫ e' ≪≫ q.symm) :
    l ≪≫ (a' ≪≫ e' ≪≫ b'.symm) = (a ≪≫ e ≪≫ b.symm) ≪≫ r := by
  have hd : q.symm ≪≫ b.symm ≪≫ r = b'.symm := by
    calc
      _ = (b ≪≫ q).symm ≪≫ r := by
        apply Iso.ext
        simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
      _ = (r ≪≫ b').symm ≪≫ r := by rw [hb]
      _ = _ := by simp
  rw [he]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc l, ← ha]
  simp only [Iso.trans_assoc, hd]

/-- A functor transports the entire conjugated comparison through commuting endpoint squares. -/
theorem iso_conjugate_refinement_map {D E : Type*} [Category* D] [Category* E]
    (G : D ⥤ E) {A B X Y : E} {A' B' X' Y' : D}
    (a : A ≅ X) (b : B ≅ Y) (a' : A' ≅ X') (b' : B' ≅ Y')
    (l : A ≅ G.obj A') (r : B ≅ G.obj B')
    (p : X ≅ G.obj X') (q : Y ≅ G.obj Y') (e : X ≅ Y) (e' : X' ≅ Y')
    (ha : a ≪≫ p = l ≪≫ G.mapIso a') (hb : b ≪≫ q = r ≪≫ G.mapIso b')
    (he : e = p ≪≫ G.mapIso e' ≪≫ q.symm) :
    l ≪≫ G.mapIso (a' ≪≫ e' ≪≫ b'.symm) = (a ≪≫ e ≪≫ b.symm) ≪≫ r := by
  simpa only [Functor.mapIso_trans, Functor.mapIso_symm] using
    iso_conjugate_refinement a b (G.mapIso a') (G.mapIso b') l r p q e (G.mapIso e') ha hb he

variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "L" => productOpenLeft n b c
local notation "R" => productOpenRight n b c
variable {U V : (normalizedProduct n b c).affineOpens} (h : U ⟶ V)
local notation "m" => productOpenComparisonMap n b c (leOfHom h)
local notation "ap" => FiniteSubgroup.CompatibleIso.curve
  (productComparisonLeftRefinement n b c (U := U) (V := V) h)
local notation "dp" => FiniteSubgroup.CompatibleIso.curve
  (productComparisonRightRefinement n b c (U := U) (V := V) h)
local notation "aV" => productComparisonLeftChartIso n b c V
local notation "dV" => productComparisonRightChartIso n b c V

/-- The named product refinement retains the full affine universal comparison. -/
theorem productAffineUniversalComparison_refine :
    affineUniversalComparison n b c (L U) (R U) =
      ap ≪≫ (baseChangeFunctor m).mapIso (affineUniversalComparison n b c (L V) (R V)) ≪≫
        (dp).symm :=
  affineUniversalComparison_overlap_conjugate n b c (L V) (R V) (L U) (R U)
    (DirectedAffineSpectrum.restriction _ (leOfHom h))
    (productOpenLeft_refine n b c (leOfHom h)) (productOpenRight_refine n b c (leOfHom h))

attribute [local irreducible] affineComparisonOverlapMap
  productComparisonLeftChartIso productComparisonRightChartIso
  productComparisonLeftRefinement productComparisonRightRefinement coverRefinementIso

/-- Pullback preserves the explicit three-factor full comparison on a product chart. -/
theorem productUniversalChartComparison_map :
    (baseChangeFunctor m).mapIso (productUniversalChartComparison n b c V) =
      (baseChangeFunctor m).mapIso aV ≪≫
        (baseChangeFunctor m).mapIso (affineUniversalComparison n b c (L V) (R V)) ≪≫
          ((baseChangeFunctor m).mapIso dV).symm := by
  simp only [productUniversalChartComparison, Functor.mapIso_trans, Functor.mapIso_symm]


end FLT.Mazur.CyclicCharacteristicAtlas
