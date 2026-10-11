/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertChartRelationPullback

/-!
# The two common-source relations are the same scheme

The original relation restricted to the common source is isomorphic to the
full chart relation pulled back along both parameter endpoints. The proof
retains both endpoints and uses the original Picard sections throughout.
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

/-- The chart bridge maps to the actual original restricted relation. -/
def variableChartBridgeToRestricted :
    variableChartRelationBridge f hL d V c ⟶ baseOpenRestrictedRelation f hL d V c :=
  (variableRestrictedRelation_lift f hL d V c
    (variableChartBridgeFst f hL d V c) (variableChartBridgeSnd f hL d V c) (by
      rw [variableSourceClass_eq_parameter, variableSourceClass_eq_parameter,
        ← variableChartBridgeToRelation_fst, ← variableChartBridgeToRelation_snd]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
        variableChartRelation_class])).choose

@[reassoc]
theorem variableChartBridgeToRestricted_fst :
    variableChartBridgeToRestricted f hL d V c ≫ baseOpenRestrictedFst f hL d V c =
      variableChartBridgeFst f hL d V c :=
  (variableRestrictedRelation_lift f hL d V c _ _ (by
    rw [variableSourceClass_eq_parameter, variableSourceClass_eq_parameter,
      ← variableChartBridgeToRelation_fst, ← variableChartBridgeToRelation_snd]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      variableChartRelation_class])).choose_spec.1.1

@[reassoc]
theorem variableChartBridgeToRestricted_snd :
    variableChartBridgeToRestricted f hL d V c ≫ baseOpenRestrictedSnd f hL d V c =
      variableChartBridgeSnd f hL d V c :=
  (variableRestrictedRelation_lift f hL d V c _ _ (by
    rw [variableSourceClass_eq_parameter, variableSourceClass_eq_parameter,
      ← variableChartBridgeToRelation_fst, ← variableChartBridgeToRelation_snd]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      variableChartRelation_class])).choose_spec.1.2

/-- The inverse comparison is the lift through both actual scheme pullbacks. -/
def variableRestrictedToChartBridge :
    baseOpenRestrictedRelation f hL d V c ⟶ variableChartRelationBridge f hL d V c :=
  pullback.lift
    (pullback.lift (variableRestrictedToChartRelation f hL d V c)
      (baseOpenRestrictedFst f hL d V c) (variableRestrictedToChartRelation_fst f hL d V c))
    (baseOpenRestrictedSnd f hL d V c) (by
      dsimp only [variableChartRelationOther]
      rw [pullback.lift_fst_assoc, variableRestrictedToChartRelation_snd])

@[reassoc]
theorem variableRestrictedToChartBridge_fst :
    variableRestrictedToChartBridge f hL d V c ≫ variableChartBridgeFst f hL d V c =
      baseOpenRestrictedFst f hL d V c := by
  dsimp only [variableRestrictedToChartBridge, variableChartBridgeFst]
  rw [pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc]
theorem variableRestrictedToChartBridge_snd :
    variableRestrictedToChartBridge f hL d V c ≫ variableChartBridgeSnd f hL d V c =
      baseOpenRestrictedSnd f hL d V c := pullback.lift_snd _ _ _

/-- The inverse comparison retains the original chart relation arrow. -/
@[reassoc]
theorem variableRestrictedToChartBridge_relation :
    variableRestrictedToChartBridge f hL d V c ≫ variableChartBridgeToRelation f hL d V c =
      variableRestrictedToChartRelation f hL d V c := by
  dsimp only [variableRestrictedToChartBridge, variableChartBridgeToRelation]
  rw [pullback.lift_fst_assoc, pullback.lift_fst]

/-- The chart bridge is determined by its two common-source endpoints. -/
theorem variableChartBridge_hom_ext {T : Over (Spec (.of R))}
    {a b : T ⟶ variableChartRelationBridge f hL d V c}
    (h₁ : a ≫ variableChartBridgeFst f hL d V c = b ≫ variableChartBridgeFst f hL d V c)
    (h₂ : a ≫ variableChartBridgeSnd f hL d V c = b ≫ variableChartBridgeSnd f hL d V c) :
    a = b := by
  have hr : a ≫ variableChartBridgeToRelation f hL d V c =
      b ≫ variableChartBridgeToRelation f hL d V c := by
    apply variableChartRelation_hom_ext f hL d V c
    · simp only [Category.assoc, variableChartBridgeToRelation_fst]
      exact congrArg (fun k ↦ k ≫ variableSourceParameter f hL d V c) h₁
    · simp only [Category.assoc, variableChartBridgeToRelation_snd]
      exact congrArg (fun k ↦ k ≫ variableSourceParameter f hL d V c) h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact hr
    · exact h₁
  · exact h₂

/-- The full chart relation and original relation give the same common-source relation scheme. -/
def variableRestrictedChartBridgeIso :
    baseOpenRestrictedRelation f hL d V c ≅ variableChartRelationBridge f hL d V c where
  hom := variableRestrictedToChartBridge f hL d V c
  inv := variableChartBridgeToRestricted f hL d V c
  hom_inv_id := by
    apply baseOpenRestricted_hom_ext f hL d V c
    · simp only [Category.assoc, variableChartBridgeToRestricted_fst,
        variableRestrictedToChartBridge_fst, Category.id_comp]
    · simp only [Category.assoc, variableChartBridgeToRestricted_snd,
        variableRestrictedToChartBridge_snd, Category.id_comp]
  inv_hom_id := by
    apply variableChartBridge_hom_ext f hL d V c
    · simp only [Category.assoc, variableRestrictedToChartBridge_fst,
        variableChartBridgeToRestricted_fst, Category.id_comp]
    · simp only [Category.assoc, variableRestrictedToChartBridge_snd,
        variableChartBridgeToRestricted_snd, Category.id_comp]

end FLT.Mazur.HilbertChart
