/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertRelationBridgeIso
public import FLT.Mazur.SchemeOpenSectionDescent

/-!
# The common-source relation smoothly covers the full chart relation

Both endpoints are lifted along the actual smooth surjective parameter map.
The resulting double base change, identified with the original restricted
relation, is therefore a smooth surjective scheme morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

instance variableChartBridgeToRelation_smooth :
    Smooth (variableChartBridgeToRelation f hL d V c).left := by
  let _ : Smooth (pullback.fst (variableChartRelationFst f hL d V c)
      (variableSourceParameter f hL d V c)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback _ _).map (Over.forget _)).flip
      (inferInstanceAs (Smooth (variableSourceParameter f hL d V c).left))
  let _ : Smooth (pullback.fst (variableChartRelationOther f hL d V c)
      (variableSourceParameter f hL d V c)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback _ _).map (Over.forget _)).flip
      (inferInstanceAs (Smooth (variableSourceParameter f hL d V c).left))
  dsimp only [variableChartBridgeToRelation, Over.comp_left]
  infer_instance

instance variableChartBridgeToRelation_surjective :
    Surjective (variableChartBridgeToRelation f hL d V c).left := by
  let _ : Surjective (pullback.fst (variableChartRelationFst f hL d V c)
      (variableSourceParameter f hL d V c)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback _ _).map (Over.forget _)).flip
      (inferInstanceAs (Surjective (variableSourceParameter f hL d V c).left))
  let _ : Surjective (pullback.fst (variableChartRelationOther f hL d V c)
      (variableSourceParameter f hL d V c)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback _ _).map (Over.forget _)).flip
      (inferInstanceAs (Surjective (variableSourceParameter f hL d V c).left))
  dsimp only [variableChartBridgeToRelation, Over.comp_left]
  infer_instance

instance variableRestrictedToChartRelation_smooth :
    Smooth (variableRestrictedToChartRelation f hL d V c).left := by
  rw [← variableRestrictedToChartBridge_relation]
  change Smooth ((variableRestrictedChartBridgeIso f hL d V c).hom.left ≫ _)
  infer_instance

instance variableRestrictedToChartRelation_surjective :
    Surjective (variableRestrictedToChartRelation f hL d V c).left := by
  rw [← variableRestrictedToChartBridge_relation]
  change Surjective ((variableRestrictedChartBridgeIso f hL d V c).hom.left ≫ _)
  infer_instance

/-- The actual relation comparison detects equality on every chart-relation open. -/
theorem variableRestrictedToChartRelation_app_injective
    (W : (variableChartRelation f hL d V c).left.Opens) :
    Function.Injective ((variableRestrictedToChartRelation f hL d V c).left.app W) :=
  SchemeEffectiveEpiSections.app_injective W

end FLT.Mazur.HilbertChart
