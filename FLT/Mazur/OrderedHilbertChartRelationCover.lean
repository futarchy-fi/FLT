/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertChartRelationBridge

/-!
# A constructed surjective etale cover of the entire chart relation

The original restricted relation is the actual double pullback of the full
parameter relation. Consequently its comparison is surjective and etale,
including pairs of parameters with different translation-base coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- Retain both source endpoints and the original parameter relation arrow. -/
def originalToChartBridge :
    restrictedRelation f hL d V c ⟶ chartRelationBridge f hL d V c :=
  pullback.lift
    (pullback.lift (fullRelationToChart f hL d V c) (restrictedFst f hL d V c)
      (fullRelationToChart_fst f hL d V c))
    (restrictedSnd f hL d V c) (by
      dsimp only [chartRelationOther]
      rw [pullback.lift_fst_assoc, fullRelationToChart_snd])

@[reassoc]
theorem originalToChartBridge_fst :
    originalToChartBridge f hL d V c ≫ chartBridgeFst f hL d V c =
      restrictedFst f hL d V c := by
  dsimp only [originalToChartBridge, chartBridgeFst]
  rw [pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc]
theorem originalToChartBridge_snd :
    originalToChartBridge f hL d V c ≫ chartBridgeSnd f hL d V c =
      restrictedSnd f hL d V c := pullback.lift_snd _ _ _

@[reassoc]
theorem originalToChartBridge_relation :
    originalToChartBridge f hL d V c ≫ chartBridgeToRelation f hL d V c =
      fullRelationToChart f hL d V c := by
  dsimp only [originalToChartBridge, chartBridgeToRelation]
  rw [pullback.lift_fst_assoc, pullback.lift_fst]

/-- The full original restriction equals the entire chart relation with both endpoints lifted. -/
def fullRelationBridgeIso :
    restrictedRelation f hL d V c ≅ chartRelationBridge f hL d V c where
  hom := originalToChartBridge f hL d V c
  inv := chartBridgeToOriginal f hL d V c
  hom_inv_id := by
    apply restricted_hom_ext f hL d V c
    · rw [Category.assoc, chartBridgeToOriginal_fst, originalToChartBridge_fst,
        Category.id_comp]
    · rw [Category.assoc, chartBridgeToOriginal_snd, originalToChartBridge_snd,
        Category.id_comp]
  inv_hom_id := by
    apply chartBridge_hom_ext f hL d V c
    · rw [Category.assoc, originalToChartBridge_fst, chartBridgeToOriginal_fst,
        Category.id_comp]
    · rw [Category.assoc, originalToChartBridge_snd, chartBridgeToOriginal_snd,
        Category.id_comp]

local instance {Y : Over (Spec (.of R))} (b : Y ⟶ variableHilbertTest f d V) :
    Etale (pullback.fst b (projection f hL d V c)).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback b (projection f hL d V c)).map (Over.forget _)).flip
    (inferInstanceAs (Etale (projection f hL d V c).left))

local instance {Y : Over (Spec (.of R))} (b : Y ⟶ variableHilbertTest f d V) :
    Surjective (pullback.fst b (projection f hL d V c)).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback b (projection f hL d V c)).map (Over.forget _)).flip
    (inferInstanceAs (Surjective (projection f hL d V c).left))

instance chartBridgeToRelation_etale : Etale (chartBridgeToRelation f hL d V c).left := by
  dsimp only [chartBridgeToRelation, Over.comp_left]
  infer_instance

instance chartBridgeToRelation_surjective :
    Surjective (chartBridgeToRelation f hL d V c).left := by
  dsimp only [chartBridgeToRelation, Over.comp_left]
  infer_instance

instance fullRelationToChart_etale : Etale (fullRelationToChart f hL d V c).left := by
  rw [← originalToChartBridge_relation, Over.comp_left]
  let _ : IsIso (originalToChartBridge f hL d V c).left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (fullRelationBridgeIso f hL d V c)).hom)
  infer_instance

instance fullRelationToChart_surjective :
    Surjective (fullRelationToChart f hL d V c).left := by
  rw [← originalToChartBridge_relation, Over.comp_left]
  let _ : IsIso (originalToChartBridge f hL d V c).left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (fullRelationBridgeIso f hL d V c)).hom)
  infer_instance

/-- Every full chart relation arrow is covered by actual original restricted relation arrows. -/
theorem fullRelationToChart_covering :
    Sieve.ofArrows (fun _ : Unit ↦ restrictedRelation f hL d V c)
      (fun _ ↦ fullRelationToChart f hL d V c) ∈
        (Scheme.fppfTopology.over (Spec (.of R))) (variableChartRelation f hL d V c) :=
  RelativeFppfRepresentedCover.covering (fullRelationToChart f hL d V c)

end FLT.Mazur.OrderedHilbertBaseOpenChart
