/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperNeighborhoodFiniteUnion
public import FLT.Mazur.ProperTranslationNeighborhoodInterior

/-!
# One constructed finite etale chart for all excluded translation coordinates

The compact image of the excluded envelope lies in one proper translation
open, by finite union. For separated etale translations this constructs a
single finite etale chart over the unchanged ground, retaining every excluded
independent envelope point. A supplied partial chart family is unnecessary.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open ProperNeighborhoodAtlas
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} (B W : Over S) [IsSeparated W.hom] [Etale W.hom]
  (U : (prod B W).left.Opens) (hU : IsCompact (U : Set (prod B W).left)ᶜ)
  (hproper : ∀ y : (prod B W).left, y ∉ U →
    (prod.snd : prod B W ⟶ W).left y ∈ locus W.hom)

include hU hproper

/-- One actual finite etale translation open contains every excluded coordinate. -/
theorem exists_single_finiteTranslationOpen :
    ∃ T : W.left.Opens, Etale (T.ι ≫ W.hom) ∧ IsFinite (T.ι ≫ W.hom) ∧
      T ≤ locus W.hom ∧ ∀ y : (prod B W).left, y ∉ U →
        (prod.snd : prod B W ⟶ W).left y ∈ T := by
  let ρ := (prod.snd : prod B W ⟶ W).left
  obtain ⟨T, hKT, he, hf, hT⟩ := exists_single_finite_etale_open W.hom
    (ρ '' (U : Set (prod B W).left)ᶜ) (hU.image ρ.continuous) (by
      rintro _ ⟨y, hy, rfl⟩
      exact hproper y hy)
  exact ⟨T, he, hf, hT, fun y hy ↦ hKT ⟨y, hy, rfl⟩⟩

/-- The single constructed chart covers every bad independent envelope point, not just a branch. -/
theorem exists_single_finiteTranslationChart :
    ∃ (T : Over S) (t : T ⟶ W), IsOpenImmersion t.left ∧
      Etale T.hom ∧ IsFinite T.hom ∧
      ∀ y : (prod B W).left, y ∉ U →
        ∃ z : (prod B T).left, (prod.map (𝟙 B) t).left z = y := by
  obtain ⟨T, he, hf, _, ht⟩ := exists_single_finiteTranslationOpen B W U hU hproper
  let E : Over S := Over.mk (T.ι ≫ W.hom)
  let t : E ⟶ W := Over.homMk T.ι
  refine ⟨E, t, inferInstanceAs (IsOpenImmersion T.ι), he, hf, fun y hy ↦ ?_⟩
  let z : E.left := ⟨(prod.snd : prod B W ⟶ W).left y, ht y hy⟩
  have H := (HilbertChart.AffineRestriction.translationProductRight_isPullback
    (B := B) t).map (Over.forget _)
  obtain ⟨q, hq, _⟩ := Scheme.exists_preimage_of_isPullback H.flip y z rfl
  exact ⟨q, hq⟩

/-- With affine ground the one constructed finite translation chart is itself affine. -/
theorem exists_single_affine_finiteTranslationChart [IsAffine S] :
    ∃ (T : Over S) (t : T ⟶ W), IsAffine T.left ∧ IsOpenImmersion t.left ∧
      Etale T.hom ∧ IsFinite T.hom ∧
      ∀ y : (prod B W).left, y ∉ U →
        ∃ z : (prod B T).left, (prod.map (𝟙 B) t).left z = y := by
  obtain ⟨T, t, ht, he, hf, hcover⟩ :=
    exists_single_finiteTranslationChart B W U hU hproper
  let _ := hf
  exact ⟨T, t, isAffine_of_isAffineHom T.hom, ht, he, hf, hcover⟩

end FLT.Mazur.SchemeTranslationNorm
