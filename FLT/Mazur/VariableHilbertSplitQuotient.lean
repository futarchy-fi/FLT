/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSplitChange
public import FLT.Mazur.RelativeRelationSplitQuotient

/-!
# Effective full chart quotients along split translation changes

For a translation pulled from an open base, a section of the translation-base
map constructs a scheme model for the FULL invariant quotient. The original
full relation and original Picard class are retained in this identification.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] (c : (relativeFppfSheaf f).obj.obj (op V))
  (s : V ⟶ W) (hs : s ≫ b = 𝟙 V)
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

/-- Each actual source parameter is related to its chosen section representative. -/
def variableHilbertSplitRelation :
    variableHilbertTest f d W ⟶ variableChartRelation f hL d W cW :=
  (variableHilbertChange_relation_lift f hL d b c (𝟙 _)
    (baseMarkedChartChange f b d ≫ baseMarkedChartChange f s d) (by
      rw [Category.assoc, variableHilbertChange_section f d b s hs,
        Category.comp_id, Category.id_comp])).choose

/-- The split relation retains the original source parameter. -/
theorem variableHilbertSplitRelation_fst :
    variableHilbertSplitRelation f hL d b c s hs ≫
      variableChartRelationFst f hL d W cW = 𝟙 _ :=
  (variableHilbertChange_relation_lift f hL d b c (𝟙 _)
    (baseMarkedChartChange f b d ≫ baseMarkedChartChange f s d) (by
      rw [Category.assoc, variableHilbertChange_section f d b s hs,
        Category.comp_id, Category.id_comp])).choose_spec.1.1

/-- Its other endpoint is the actual representative on the section. -/
theorem variableHilbertSplitRelation_snd :
    variableHilbertSplitRelation f hL d b c s hs ≫
      variableChartRelationSnd f hL d W cW =
        baseMarkedChartChange f b d ≫ baseMarkedChartChange f s d :=
  (variableHilbertChange_relation_lift f hL d b c (𝟙 _)
    (baseMarkedChartChange f b d ≫ baseMarkedChartChange f s d) (by
      rw [Category.assoc, variableHilbertChange_section f d b s hs,
        Category.comp_id, Category.id_comp])).choose_spec.1.2

/-- The full invariant quotient has a constructed scheme model, without a scheme assumption. -/
def variableHilbertSplitQuotientIso :
    invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d W cW) ≅
      (variableHilbertTest f d V).left.toLocallyRingedSpace :=
  splitInvariantQuotientIso (variableChartEquivalenceRelation f hL d W cW)
    (baseMarkedChartChange f b d) (baseMarkedChartChange f s d)
    (variableHilbertChange_condition f hL d b c) (variableHilbertChange_section f d b s hs)
    (variableHilbertSplitRelation f hL d b c s hs)
    (variableHilbertSplitRelation_fst f hL d b c s hs)
    (variableHilbertSplitRelation_snd f hL d b c s hs)

/-- This full quotient identification is induced by the original chart comparison. -/
theorem variableHilbertSplitQuotientIso_projection :
    invariantLocallyRingedProjection (variableChartEquivalenceRelation f hL d W cW) ≫
      (variableHilbertSplitQuotientIso f hL d b c s hs).hom =
        (baseMarkedChartChange f b d).left.toLRSHom :=
  splitInvariantQuotientIso_projection _ _ _ _ _ _ _ _

/-- Its structure map is the original quotient structure map. -/
theorem variableHilbertSplitQuotientIso_baseMap :
    (variableHilbertSplitQuotientIso f hL d b c s hs).hom ≫
      (variableHilbertTest f d V).hom.toLRSHom =
        invariantLocallyRingedBaseMap (variableChartEquivalenceRelation f hL d W cW) :=
  splitInvariantQuotientIso_baseMap _ _ _ _ _ _ _ _

end FLT.Mazur.HilbertChart
