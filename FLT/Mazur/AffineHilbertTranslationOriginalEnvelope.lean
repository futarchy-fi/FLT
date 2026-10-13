/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationFullRestriction

/-!
# The original envelope map on constructed translation refinements

Both endpoints map to the original source. The independent product map changes
both the source and the translation, with no monicity requirement.
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
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "u" => translationSourceMap f d b k
local notation "l" => translationSourceChart f d b k
local notation "c'" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "p'" => fst f hL d W c' l
local notation "q'" => snd f hL d W c' l

/-- The actual original full relation arrow on the constructed source refinement. -/
def translationSourceRelationMap : relation f hL d W c' l ⟶ relation f hL d V c k :=
  arrow f hL d V c k (p' ≫ u) (q' ≫ u)
    ((translationSource_equal_class_iff f hL d b c k p' q').mpr
      (equal_class f hL d W c' l))

@[reassoc]
theorem translationSourceRelationMap_fst :
    translationSourceRelationMap f hL d b c k ≫ p = p' ≫ u :=
  arrow_fst f hL d V c k _ _ _

@[reassoc]
theorem translationSourceRelationMap_snd :
    translationSourceRelationMap f hL d b c k ≫ q = q' ≫ u :=
  arrow_snd f hL d V c k _ _ _

/-- Both independent coordinates are retained in the original envelope square. -/
theorem translationSourceEnvelope_square :
    translationSourceRelationMap f hL d b c k ≫ toEnvelope f hL d V c k =
      toEnvelope f hL d W c' l ≫ prod.map u b := by
  apply prod.hom_ext
  · simp only [Category.assoc, toEnvelope_test, prod.map_fst,
      translationSourceRelationMap_snd, toEnvelope_test_assoc]
  · simp only [Category.assoc, toEnvelope_base, prod.map_snd,
      translationSourceRelationMap_fst_assoc, toEnvelope_base_assoc]
    rw [← Category.assoc u k, translationSource_square, Category.assoc,
      baseMarkedChartChange_base]

variable {T : Over (Spec (.of R))} (r : T ⟶ relation f hL d V c k)
  (e : T ⟶ prod (translationSource f d b k) W)
  (h : r ≫ toEnvelope f hL d V c k =
    e ≫ prod.map (translationSourceMap f d b k) b)

include h in
/-- The original first endpoint and the new translation satisfy the source pullback equation. -/
theorem translationEnvelopeCone_base :
    (r ≫ p) ≫ k ≫ variableHilbertBase f d V = (e ≫ prod.snd) ≫ b := by
  have H := congrArg (fun t => t ≫ prod.snd) h
  simpa only [Category.assoc, toEnvelope_base, prod.map_snd] using H

/-- The actual lifted first endpoint is constructed from the source pullback square. -/
def translationEnvelopeConeFirst : T ⟶ translationSource f d b k :=
  (translationSource_isPullback f d b k).lift (r ≫ p) (e ≫ prod.snd)
    (translationEnvelopeCone_base f hL d b c k r e h)

@[reassoc]
theorem translationEnvelopeConeFirst_source :
    translationEnvelopeConeFirst f hL d b c k r e h ≫ u = r ≫ p :=
  (translationSource_isPullback f d b k).lift_fst _ _ _

@[reassoc]
theorem translationEnvelopeConeFirst_base :
    translationEnvelopeConeFirst f hL d b c k r e h ≫ l ≫
      variableHilbertBase f d W = e ≫ prod.snd :=
  (translationSource_isPullback f d b k).lift_snd _ _ _

include h in
/-- The second endpoint is the independent refined-source coordinate of the cone. -/
theorem translationEnvelopeCone_second : r ≫ q = (e ≫ prod.fst) ≫ u := by
  have H := congrArg (fun t => t ≫ prod.fst) h
  simpa only [Category.assoc, toEnvelope_test, prod.map_fst] using H

end FLT.Mazur.HilbertChart.AffineRestriction
