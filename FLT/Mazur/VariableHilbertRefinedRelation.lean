/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertChangeFppf
public import FLT.Mazur.VariableHilbertChartRelationOperations

/-!
# The full parameter relation under arbitrary translation refinement

Changing the translation base pulls back both independent endpoints of the
entire equal-class relation. This includes mixed translation coordinates and
requires neither an open translation base nor a descended quotient scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.VariableHilbertFppfRefinement
open HilbertChart CartierAbel SchemePicard FCurve
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
local notation "p" => variableChartRelationFst f hL d V c
local notation "q" => variableChartRelationSnd f hL d V c
local notation "p'" => variableChartRelationFst f hL d W cW
local notation "q'" => variableChartRelationSnd f hL d W cW

/-- Original Picard classes commute with arbitrary translation-base refinement. -/
theorem class_map {T : Over (Spec (.of R))} (a : T ⟶ variableHilbertTest f d W) :
    (relativeFppfSheaf f).obj.map (a ≫ g).op (variableChartSection f hL d V c) =
      (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d W cW) := by
  rw [variableChartSection_map, variableChartSection_map]
  exact baseMarkedChartChange_class f hL b (d, c) a

/-- Refine the full relation, preserving both independent endpoint maps. -/
def relationMap : variableChartRelation f hL d W cW ⟶ variableChartRelation f hL d V c :=
  variableChartRelationLift f hL d V c (p' ≫ g) (q' ≫ g) (by
    rw [class_map, class_map]
    exact variableChartRelation_class f hL d W cW)

@[reassoc]
theorem relationMap_fst : relationMap f hL d b c ≫ p = p' ≫ g :=
  variableChartRelationLift_fst f hL d V c _ _ _

@[reassoc]
theorem relationMap_snd : relationMap f hL d b c ≫ q = q' ≫ g :=
  variableChartRelationLift_snd f hL d V c _ _ _

/-- Lift the first parameter endpoint to the changed translation base. -/
def first : Over (Spec (.of R)) := pullback p g

/-- Keep the independent second parameter endpoint. -/
def other : first f hL d b c ⟶ variableHilbertTest f d V := pullback.fst p g ≫ q

/-- Lift the second endpoint independently of the first. -/
def bridge : Over (Spec (.of R)) := pullback (other f hL d b c) g

/-- The first changed endpoint. -/
def fst : bridge f hL d b c ⟶ variableHilbertTest f d W :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- The second changed endpoint. -/
def snd : bridge f hL d b c ⟶ variableHilbertTest f d W := pullback.snd _ _

/-- The full original relation arrow underlying the lifted pair. -/
def toRelation : bridge f hL d b c ⟶ variableChartRelation f hL d V c :=
  pullback.fst _ _ ≫ pullback.fst _ _

@[reassoc]
theorem toRelation_fst : toRelation f hL d b c ≫ p = fst f hL d b c ≫ g := by
  dsimp only [toRelation, fst]
  rw [Category.assoc, pullback.condition, ← Category.assoc]

@[reassoc]
theorem toRelation_snd : toRelation f hL d b c ≫ q = snd f hL d b c ≫ g := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _ = pullback.snd _ _ ≫ _
  rw [Category.assoc]
  exact pullback.condition

/-- Both lifted parameters have the same original Picard class. -/
theorem bridge_class :
    (relativeFppfSheaf f).obj.map (fst f hL d b c).op
      (variableChartSection f hL d W cW) =
    (relativeFppfSheaf f).obj.map (snd f hL d b c).op
      (variableChartSection f hL d W cW) := by
  rw [← class_map, ← class_map, ← toRelation_fst, ← toRelation_snd]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    variableChartRelation_class]

/-- The entire double pullback maps back to the original changed relation. -/
def fromBridge : bridge f hL d b c ⟶ variableChartRelation f hL d W cW :=
  variableChartRelationLift f hL d W cW _ _ (bridge_class f hL d b c)

@[reassoc]
theorem fromBridge_fst : fromBridge f hL d b c ≫ p' = fst f hL d b c :=
  variableChartRelationLift_fst f hL d W cW _ _ _

@[reassoc]
theorem fromBridge_snd : fromBridge f hL d b c ≫ q' = snd f hL d b c :=
  variableChartRelationLift_snd f hL d W cW _ _ _

/-- The changed relation supplies the original relation arrow and both independent lifts. -/
def toBridge : variableChartRelation f hL d W cW ⟶ bridge f hL d b c :=
  pullback.lift
    (pullback.lift (relationMap f hL d b c) p' (relationMap_fst f hL d b c)) q' (by
      dsimp only [other]
      rw [pullback.lift_fst_assoc, relationMap_snd])

@[reassoc]
theorem toBridge_fst : toBridge f hL d b c ≫ fst f hL d b c = p' := by
  dsimp only [toBridge, fst]
  rw [pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc]
theorem toBridge_snd : toBridge f hL d b c ≫ snd f hL d b c = q' :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem toBridge_relation :
    toBridge f hL d b c ≫ toRelation f hL d b c = relationMap f hL d b c := by
  dsimp only [toBridge, toRelation]
  rw [pullback.lift_fst_assoc, pullback.lift_fst]

/-- Both changed endpoints determine the full double-pullback arrow. -/
theorem bridge_hom_ext {T : Over (Spec (.of R))} {a a' : T ⟶ bridge f hL d b c}
    (h₁ : a ≫ fst f hL d b c = a' ≫ fst f hL d b c)
    (h₂ : a ≫ snd f hL d b c = a' ≫ snd f hL d b c) : a = a' := by
  have hr : a ≫ toRelation f hL d b c = a' ≫ toRelation f hL d b c := by
    apply variableChartRelation_hom_ext f hL d V c
    · simp only [Category.assoc, toRelation_fst]
      exact congrArg (fun k ↦ k ≫ g) h₁
    · simp only [Category.assoc, toRelation_snd]
      exact congrArg (fun k ↦ k ≫ g) h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact hr
    · exact h₁
  · exact h₂

/-- Arbitrary translation refinement pulls back the full relation in both coordinates. -/
def bridgeIso : variableChartRelation f hL d W cW ≅ bridge f hL d b c where
  hom := toBridge f hL d b c
  inv := fromBridge f hL d b c
  hom_inv_id := by
    apply variableChartRelation_hom_ext f hL d W cW
    · rw [Category.assoc, fromBridge_fst, toBridge_fst, Category.id_comp]
    · rw [Category.assoc, fromBridge_snd, toBridge_snd, Category.id_comp]
  inv_hom_id := by
    apply bridge_hom_ext f hL d b c
    · rw [Category.assoc, toBridge_fst, fromBridge_fst, Category.id_comp]
    · rw [Category.assoc, toBridge_snd, fromBridge_snd, Category.id_comp]

end FLT.Mazur.VariableHilbertFppfRefinement
