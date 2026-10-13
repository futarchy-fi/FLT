/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationRelation
public import FLT.Mazur.SchemeRelationIsoInvariants

/-!
# Independent envelopes and invariant rings under translation refinement

The unchanged full relation embeds into the smaller independent-translation
product. The envelope square is Cartesian for monic translation changes,
while every original invariant source coefficient is retained literally.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {B : Over (Spec (.of R))} (l : B ⟶ variableHilbertTest f d W)
local notation "c'" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "k" => l ≫ baseMarkedChartChange f b d

/-- The full relation comparison retains both independent envelope coordinates. -/
theorem translationEnvelope_square :
    translationRelationMap f hL d b c l ≫ toEnvelope f hL d V c k =
      toEnvelope f hL d W c' l ≫ prod.map (𝟙 B) b := by
  apply prod.hom_ext
  · simp only [Category.assoc, toEnvelope_test, prod.map_fst, Category.comp_id,
      translationRelationMap_snd]
  · simp only [Category.assoc, toEnvelope_base, prod.map_snd,
      translationRelationMap_fst_assoc, baseMarkedChartChange_base, toEnvelope_base_assoc]

/-- A genuine monic translation refinement cuts out the entire original relation. -/
theorem translationEnvelope_isPullback [Mono b] :
    IsPullback (translationRelationMap f hL d b c l).left
      (toEnvelope f hL d W c' l).left (toEnvelope f hL d V c k).left
      (prod.map (𝟙 B) b).left := by
  let _ : IsIso (translationRelationMap f hL d b c l).left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (translationRelationIso f hL d b c l)).hom)
  exact IsPullback.of_horiz_isIso_mono
    ⟨congrArg Over.Hom.left (translationEnvelope_square f hL d b c l)⟩

/-- The original and refined full relations define the SAME invariant coefficient subring. -/
theorem translation_compatibleFunctions :
    SchemeEffectiveEpiSections.compatibleFunctions (fst f hL d V c k).left
        (snd f hL d V c k).left =
      SchemeEffectiveEpiSections.compatibleFunctions (fst f hL d W c' l).left
        (snd f hL d W c' l).left :=
  SchemeEffectiveEpiSections.relationIso_compatibleFunctions _ _ _ _
    ((Over.forget _).mapIso (translationRelationIso f hL d b c l))
    (congrArg Over.Hom.left (translationRelationMap_fst f hL d b c l))
    (congrArg Over.Hom.left (translationRelationMap_snd f hL d b c l))

/-- Invariant source neighborhoods are unchanged even though the translation envelope shrinks. -/
theorem translation_invariantOpen_iff (U : B.left.Opens) :
    (fst f hL d V c k).left ⁻¹ᵁ U = (snd f hL d V c k).left ⁻¹ᵁ U ↔
      (fst f hL d W c' l).left ⁻¹ᵁ U = (snd f hL d W c' l).left ⁻¹ᵁ U :=
  SchemeEffectiveEpiSections.relationIso_invariantOpen_iff _ _ _ _
    ((Over.forget _).mapIso (translationRelationIso f hL d b c l))
    (congrArg Over.Hom.left (translationRelationMap_fst f hL d b c l))
    (congrArg Over.Hom.left (translationRelationMap_snd f hL d b c l)) U

end FLT.Mazur.HilbertChart.AffineRestriction
