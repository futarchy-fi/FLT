/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertChartFullRelation

/-!
# Full relation comparison with both chart endpoints lifted

The full original relation restricted to a translated chart is isomorphic
to the double pullback of its full parameter relation. The construction
works on arbitrary translation bases and preserves every mixed component.
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

/-- Lift the first actual parameter endpoint along the constructed etale cover. -/
def chartRelationFirst : Over (Spec (.of R)) :=
  pullback (variableChartRelationFst f hL d V c) (projection f hL d V c)

/-- Retain the independent second parameter. -/
def chartRelationOther : chartRelationFirst f hL d V c ⟶ variableHilbertTest f d V :=
  pullback.fst _ _ ≫ variableChartRelationSnd f hL d V c

/-- Lift both endpoints of the entire chart relation. -/
def chartRelationBridge : Over (Spec (.of R)) :=
  pullback (chartRelationOther f hL d V c) (projection f hL d V c)

/-- The first lifted endpoint. -/
def chartBridgeFst : chartRelationBridge f hL d V c ⟶ source f hL d V c :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- The second lifted endpoint. -/
def chartBridgeSnd : chartRelationBridge f hL d V c ⟶ source f hL d V c :=
  pullback.snd _ _

/-- The full relation arrow underlying the two lifted endpoints. -/
def chartBridgeToRelation :
    chartRelationBridge f hL d V c ⟶ variableChartRelation f hL d V c :=
  pullback.fst _ _ ≫ pullback.fst _ _

@[reassoc]
theorem chartBridgeToRelation_fst :
    chartBridgeToRelation f hL d V c ≫ variableChartRelationFst f hL d V c =
      chartBridgeFst f hL d V c ≫ projection f hL d V c := by
  dsimp only [chartBridgeToRelation, chartBridgeFst]
  rw [Category.assoc, pullback.condition, ← Category.assoc]

@[reassoc]
theorem chartBridgeToRelation_snd :
    chartBridgeToRelation f hL d V c ≫ variableChartRelationSnd f hL d V c =
      chartBridgeSnd f hL d V c ≫ projection f hL d V c := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _ = pullback.snd _ _ ≫ _
  rw [Category.assoc]
  exact pullback.condition

/-- Both lifted endpoints recover equal original classes. -/
theorem chartBridge_class :
    (relativeFppfSheaf f).obj.map
      (chartBridgeFst f hL d V c ≫ inclusion f hL d V c).op
        (OrderedHilbertIdentityOriginalSection.sourceSection f hL) =
    (relativeFppfSheaf f).obj.map
      (chartBridgeSnd f hL d V c ≫ inclusion f hL d V c).op
        (OrderedHilbertIdentityOriginalSection.sourceSection f hL) := by
  rw [full_parameter_class, full_parameter_class,
    ← chartBridgeToRelation_fst, ← chartBridgeToRelation_snd]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    variableChartRelation_class]

/-- Recover the actual original restricted relation from the full chart relation. -/
def chartBridgeToOriginal :
    chartRelationBridge f hL d V c ⟶ restrictedRelation f hL d V c :=
  (full_restricted_lift f hL d V c _ _ (chartBridge_class f hL d V c)).choose

@[reassoc]
theorem chartBridgeToOriginal_fst :
    chartBridgeToOriginal f hL d V c ≫ restrictedFst f hL d V c =
      chartBridgeFst f hL d V c :=
  (full_restricted_lift f hL d V c _ _ (chartBridge_class f hL d V c)).choose_spec.1.1

@[reassoc]
theorem chartBridgeToOriginal_snd :
    chartBridgeToOriginal f hL d V c ≫ restrictedSnd f hL d V c =
      chartBridgeSnd f hL d V c :=
  (full_restricted_lift f hL d V c _ _ (chartBridge_class f hL d V c)).choose_spec.1.2

/-- A bridge arrow is determined by its two lifted source endpoints. -/
theorem chartBridge_hom_ext {T : Over (Spec (.of R))}
    {a b : T ⟶ chartRelationBridge f hL d V c}
    (h₁ : a ≫ chartBridgeFst f hL d V c = b ≫ chartBridgeFst f hL d V c)
    (h₂ : a ≫ chartBridgeSnd f hL d V c = b ≫ chartBridgeSnd f hL d V c) : a = b := by
  have hr : a ≫ chartBridgeToRelation f hL d V c =
      b ≫ chartBridgeToRelation f hL d V c := by
    apply variableChartRelation_hom_ext f hL d V c
    · simp only [Category.assoc, chartBridgeToRelation_fst]
      exact congrArg (fun k ↦ k ≫ projection f hL d V c) h₁
    · simp only [Category.assoc, chartBridgeToRelation_snd]
      exact congrArg (fun k ↦ k ≫ projection f hL d V c) h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact hr
    · exact h₁
  · exact h₂

end FLT.Mazur.OrderedHilbertBaseOpenChart
