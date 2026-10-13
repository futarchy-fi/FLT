/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertRefinedRelation
public import FLT.Mazur.RelativeRelationFppfRefinement

/-!
# Full invariant Hilbert quotients are unchanged by fppf translation refinement

The source cover and double-pullback relation cover are actual fppf maps.
They identify the full locally ringed coequalizers, retaining every invariant
function and the coefficient map, for arbitrary original translation bases.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.VariableHilbertFppfRefinement
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "g" => baseMarkedChartChange f b d
local notation "P" => variableChartRelationFst f hL d V c
local notation "Q" => variableChartRelationSnd f hL d V c
local notation "P₁" => variableChartRelationFst f hL d W cW
local notation "Q₁" => variableChartRelationSnd f hL d W cW

local instance [Flat b.left] {Y : Over (Spec (.of R))} (a : Y ⟶ variableHilbertTest f d V) :
    Flat (pullback.fst a g).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback a g).map (Over.forget _)).flip
    (inferInstanceAs (Flat (g).left))

local instance [LocallyOfFinitePresentation b.left] {Y : Over (Spec (.of R))}
    (a : Y ⟶ variableHilbertTest f d V) : LocallyOfFinitePresentation (pullback.fst a g).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback a g).map (Over.forget _)).flip
    (inferInstanceAs (LocallyOfFinitePresentation (g).left))

local instance [Surjective b.left] {Y : Over (Spec (.of R))}
    (a : Y ⟶ variableHilbertTest f d V) : Surjective (pullback.fst a g).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback a g).map (Over.forget _)).flip
    (inferInstanceAs (Surjective (g).left))

instance relationMap_flat [Flat b.left] : Flat (relationMap f hL d b c).left := by
  rw [← toBridge_relation, Over.comp_left]
  let _ : IsIso (toBridge f hL d b c).left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (bridgeIso f hL d b c)).hom)
  let _ : Flat (toRelation f hL d b c).left := by
    dsimp only [toRelation, Over.comp_left]
    infer_instance
  infer_instance

instance relationMap_locallyOfFinitePresentation [LocallyOfFinitePresentation b.left] :
    LocallyOfFinitePresentation (relationMap f hL d b c).left := by
  rw [← toBridge_relation, Over.comp_left]
  let _ : IsIso (toBridge f hL d b c).left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (bridgeIso f hL d b c)).hom)
  let _ : LocallyOfFinitePresentation (toRelation f hL d b c).left := by
    dsimp only [toRelation, Over.comp_left]
    infer_instance
  infer_instance

instance relationMap_surjective [Surjective b.left] :
    Surjective (relationMap f hL d b c).left := by
  rw [← toBridge_relation, Over.comp_left]
  let _ : IsIso (toBridge f hL d b c).left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (bridgeIso f hL d b c)).hom)
  let _ : Surjective (toRelation f hL d b c).left := by
    dsimp only [toRelation, Over.comp_left]
    infer_instance
  infer_instance

/-- The actual source kernel pair maps into the whole changed relation. -/
def kernelToRelation : pullback g g ⟶ variableChartRelation f hL d W cW :=
  variableChartRelationLift f hL d W cW (pullback.fst g g) (pullback.snd g g) (by
    rw [← class_map, ← class_map, pullback.condition])

@[reassoc]
theorem kernelToRelation_fst : kernelToRelation f hL d b c ≫ P₁ = pullback.fst g g :=
  variableChartRelationLift_fst f hL d W cW _ _ _

@[reassoc]
theorem kernelToRelation_snd : kernelToRelation f hL d b c ≫ Q₁ = pullback.snd g g :=
  variableChartRelationLift_snd f hL d W cW _ _ _

variable [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]

/-- Fppf translation refinement preserves the full locally ringed coequalizer. -/
def quotientIso : locallyRingedQuotient (p := P₁) (q := Q₁) ≅
    locallyRingedQuotient (p := P) (q := Q) :=
  RelativeRelationFppfRefinement.quotientIso P₁ Q₁ P Q g
    (relationMap f hL d b c) (relationMap_fst f hL d b c) (relationMap_snd f hL d b c)
    (kernelToRelation f hL d b c) (kernelToRelation_fst f hL d b c)
    (kernelToRelation_snd f hL d b c)

/-- The full quotient comparison has precisely the actual parameter map as its source. -/
@[reassoc]
theorem quotientIso_source :
    locallyRingedProjection (p := P₁) (q := Q₁) ≫ (quotientIso f hL d b c).hom =
      (g).left.toLRSHom ≫ locallyRingedProjection (p := P) (q := Q) :=
  RelativeRelationFppfRefinement.quotientIso_source _ _ _ _ _ _ _ _ _ _ _

/-- Original coefficient maps survive the full coequalizer comparison. -/
theorem quotientIso_base :
    (quotientIso f hL d b c).hom ≫ locallyRingedBaseMap (p := P) (q := Q) =
      locallyRingedBaseMap (p := P₁) (q := Q₁) :=
  RelativeRelationFppfRefinement.quotientIso_base _ _ _ _ _ _ _ _ _ _ _

/-- All original invariant functions are preserved on every open of either quotient. -/
def invariantIso :
    invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d W cW) ≅
      invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL d V c) :=
  (invariantLocallyRingedIso (variableChartEquivalenceRelation f hL d W cW)).symm ≪≫
    quotientIso f hL d b c ≪≫
      invariantLocallyRingedIso (variableChartEquivalenceRelation f hL d V c)

/-- The explicit invariant comparison preserves the geometric source map. -/
@[reassoc]
theorem invariantIso_source :
    invariantLocallyRingedProjection (variableChartEquivalenceRelation f hL d W cW) ≫
      (invariantIso f hL d b c).hom = (g).left.toLRSHom ≫
        invariantLocallyRingedProjection (variableChartEquivalenceRelation f hL d V c) := by
  dsimp only [invariantIso, Iso.trans_hom, Iso.symm_hom, invariantLocallyRingedProjection]
  rw [Category.assoc, Iso.hom_inv_id_assoc, quotientIso_source_assoc]

/-- The explicit invariant comparison retains the exact original coefficient map. -/
theorem invariantIso_base :
    (invariantIso f hL d b c).hom ≫
      invariantLocallyRingedBaseMap (variableChartEquivalenceRelation f hL d V c) =
        invariantLocallyRingedBaseMap (variableChartEquivalenceRelation f hL d W cW) := by
  dsimp only [invariantIso, Iso.trans_hom, Iso.symm_hom, invariantLocallyRingedBaseMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, quotientIso_base]

end FLT.Mazur.VariableHilbertFppfRefinement
