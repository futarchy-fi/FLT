/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertRelationBridge

/-!
# Pulling the chart relation back to the original common source

Both parameter endpoints are lifted by actual scheme pullbacks. Equality of
the chart's original Picard classes then constructs an original relation
arrow. Point lifting uses scheme fiber products, including residue extensions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- Lift the first endpoint of the chart relation to the original common source. -/
def variableChartRelationFirst : Over (Spec (.of R)) :=
  pullback (variableChartRelationFst f hL d V c) (variableSourceParameter f hL d V c)

/-- The second actual parameter endpoint after the first lift. -/
def variableChartRelationOther :
    variableChartRelationFirst f hL d V c ⟶ variableHilbertTest f d V :=
  pullback.fst _ _ ≫ variableChartRelationSnd f hL d V c

/-- The chart relation with both endpoints lifted to the common source. -/
def variableChartRelationBridge : Over (Spec (.of R)) :=
  pullback (variableChartRelationOther f hL d V c) (variableSourceParameter f hL d V c)

/-- Its first common-source endpoint. -/
def variableChartBridgeFst :
    variableChartRelationBridge f hL d V c ⟶ variableSourceIntersection f hL d V c :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- Its second common-source endpoint. -/
def variableChartBridgeSnd :
    variableChartRelationBridge f hL d V c ⟶ variableSourceIntersection f hL d V c :=
  pullback.snd _ _

/-- The actual chart relation arrow retained by the double pullback. -/
def variableChartBridgeToRelation :
    variableChartRelationBridge f hL d V c ⟶ variableChartRelation f hL d V c :=
  pullback.fst _ _ ≫ pullback.fst _ _

/-- The first endpoint square commutes as scheme morphisms. -/
@[reassoc]
theorem variableChartBridgeToRelation_fst :
    variableChartBridgeToRelation f hL d V c ≫ variableChartRelationFst f hL d V c =
      variableChartBridgeFst f hL d V c ≫ variableSourceParameter f hL d V c := by
  dsimp only [variableChartBridgeToRelation, variableChartBridgeFst]
  rw [Category.assoc, pullback.condition, ← Category.assoc]

/-- The second endpoint square commutes as scheme morphisms. -/
@[reassoc]
theorem variableChartBridgeToRelation_snd :
    variableChartBridgeToRelation f hL d V c ≫ variableChartRelationSnd f hL d V c =
      variableChartBridgeSnd f hL d V c ≫ variableSourceParameter f hL d V c := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _ = pullback.snd _ _ ≫ _
  rw [Category.assoc]
  exact pullback.condition

/-- The full chart relation lifts to the actual original relation on the common source. -/
def variableChartBridgeToOriginal :
    variableChartRelationBridge f hL d V c ⟶ smoothHilbertRelation f hL :=
  smoothHilbertRelationLift f hL
    (variableChartBridgeFst f hL d V c ≫ variableSourceInclusion f hL d V c)
    (variableChartBridgeSnd f hL d V c ≫ variableSourceInclusion f hL d V c) (by
      rw [variableSourceClass_eq_parameter, variableSourceClass_eq_parameter,
        ← variableChartBridgeToRelation_fst, ← variableChartBridgeToRelation_snd]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
        variableChartRelation_class])

/-- The lifted original relation has the prescribed first source endpoint. -/
theorem variableChartBridgeToOriginal_fst :
    variableChartBridgeToOriginal f hL d V c ≫ smoothHilbertRelationFst f hL =
      variableChartBridgeFst f hL d V c ≫ variableSourceInclusion f hL d V c :=
  smoothHilbertRelationLift_fst f hL _ _ _

/-- The lifted original relation has the prescribed second source endpoint. -/
theorem variableChartBridgeToOriginal_snd :
    variableChartBridgeToOriginal f hL d V c ≫ smoothHilbertRelationSnd f hL =
      variableChartBridgeSnd f hL d V c ≫ variableSourceInclusion f hL d V c :=
  smoothHilbertRelationLift_snd f hL _ _ _

/-- A chart relation between parameter images lifts to the double scheme pullback. -/
theorem variableChartBridge_point_lift (x y : (variableSourceIntersection f hL d V c).left)
    (a : (variableChartRelation f hL d V c).left)
    (ha : (variableChartRelationFst f hL d V c).left a =
      (variableSourceParameter f hL d V c).left x)
    (hb : (variableChartRelationSnd f hL d V c).left a =
      (variableSourceParameter f hL d V c).left y) :
    ∃ z : (variableChartRelationBridge f hL d V c).left,
      (variableChartBridgeFst f hL d V c).left z = x ∧
        (variableChartBridgeSnd f hL d V c).left z = y := by
  have H₁ := (IsPullback.of_hasPullback
    (variableChartRelationFst f hL d V c) (variableSourceParameter f hL d V c)).map (Over.forget _)
  obtain ⟨b, hb₁, hb₂⟩ := Scheme.exists_preimage_of_isPullback H₁ a x ha
  have he : (variableChartRelationOther f hL d V c).left b =
      (variableSourceParameter f hL d V c).left y :=
    (congrArg (variableChartRelationSnd f hL d V c).left hb₁).trans hb
  have H₂ := (IsPullback.of_hasPullback
    (variableChartRelationOther f hL d V c) (variableSourceParameter f hL d V c)).map
      (Over.forget _)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback H₂ b y he
  refine ⟨z, ?_, hz₂⟩
  exact (congrArg (pullback.snd (variableChartRelationFst f hL d V c)
    (variableSourceParameter f hL d V c)).left hz₁).trans hb₂

end FLT.Mazur.HilbertChart
