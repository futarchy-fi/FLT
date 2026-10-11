/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertChartRelation
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# The internal equivalence relation on each actual variable Hilbert chart

Reflexivity, symmetry, and composition are constructed as actual scheme maps
from equality of the original Picard classes, retaining the full relation
between parameters over distinct translation-base points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The unique actual relation map of two equal-class source morphisms. -/
def variableChartRelationLift {T : Over (Spec (.of R))}
    (a b : T ⟶ variableHilbertTest f d V)
    (h : (relativeFppfSheaf f).obj.map a.op (variableChartSection f hB d V c) =
      (relativeFppfSheaf f).obj.map b.op (variableChartSection f hB d V c)) :
    T ⟶ variableChartRelation f hB d V c :=
  (variableChartRelation_lift f hB d V c a b h).choose

/-- The first projection of the constructed relation map. -/
theorem variableChartRelationLift_fst {T : Over (Spec (.of R))}
    (a b : T ⟶ variableHilbertTest f d V) (h) :
    variableChartRelationLift f hB d V c a b h ≫ variableChartRelationFst f hB d V c = a :=
  (variableChartRelation_lift f hB d V c a b h).choose_spec.1.1

/-- The second projection of the constructed relation map. -/
theorem variableChartRelationLift_snd {T : Over (Spec (.of R))}
    (a b : T ⟶ variableHilbertTest f d V) (h) :
    variableChartRelationLift f hB d V c a b h ≫ variableChartRelationSnd f hB d V c = b :=
  (variableChartRelation_lift f hB d V c a b h).choose_spec.1.2

/-- The diagonal relation morphism is constructed from equality with itself. -/
def variableChartRelationRefl : variableHilbertTest f d V ⟶ variableChartRelation f hB d V c :=
  variableChartRelationLift f hB d V c (𝟙 _) (𝟙 _) rfl

/-- The inverse relation morphism exchanges the actual projections. -/
def variableChartRelationSwap :
    variableChartRelation f hB d V c ⟶ variableChartRelation f hB d V c :=
  variableChartRelationLift f hB d V c (variableChartRelationSnd f hB d V c)
    (variableChartRelationFst f hB d V c) (variableChartRelation_class f hB d V c).symm

/-- Equality of original classes is transitive on the actual composable-pair scheme. -/
theorem variableChartRelation_composable_class :
    (relativeFppfSheaf f).obj.map
      (pullback.fst (variableChartRelationSnd f hB d V c) (variableChartRelationFst f hB d V c) ≫
        variableChartRelationFst f hB d V c).op (variableChartSection f hB d V c) =
    (relativeFppfSheaf f).obj.map
      (pullback.snd (variableChartRelationSnd f hB d V c) (variableChartRelationFst f hB d V c) ≫
        variableChartRelationSnd f hB d V c).op (variableChartSection f hB d V c) := by
  calc
    _ = (relativeFppfSheaf f).obj.map
        (pullback.fst (variableChartRelationSnd f hB d V c) (variableChartRelationFst f hB d V c) ≫
          variableChartRelationSnd f hB d V c).op (variableChartSection f hB d V c) := by
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      rw [variableChartRelation_class]
    _ = (relativeFppfSheaf f).obj.map
        (pullback.snd (variableChartRelationSnd f hB d V c) (variableChartRelationFst f hB d V c) ≫
          variableChartRelationFst f hB d V c).op (variableChartSection f hB d V c) := by
      rw [pullback.condition]
    _ = _ := by
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      rw [variableChartRelation_class]

/-- Composition is an actual scheme morphism from the composable-pair pullback. -/
def variableChartRelationComp :
    Limits.pullback (variableChartRelationSnd f hB d V c) (variableChartRelationFst f hB d V c) ⟶
      variableChartRelation f hB d V c :=
  variableChartRelationLift f hB d V c (pullback.fst _ _ ≫ variableChartRelationFst f hB d V c)
    (pullback.snd _ _ ≫ variableChartRelationSnd f hB d V c)
    (variableChartRelation_composable_class f hB d V c)

/-- The represented original equal-class relation is an internal equivalence relation. -/
def variableChartEquivalenceRelation :
    CategoryTheory.EquivalenceRelation
      (variableChartRelationFst f hB d V c) (variableChartRelationSnd f hB d V c) where
  right_cancellation _ _ _ h₁ h₂ := variableChartRelation_hom_ext f hB d V c h₁ h₂
  r := variableChartRelationRefl f hB d V c
  reflexivity₁ := variableChartRelationLift_fst f hB d V c _ _ _
  reflexivity₂ := variableChartRelationLift_snd f hB d V c _ _ _
  s := variableChartRelationSwap f hB d V c
  symmetry₁ := variableChartRelationLift_fst f hB d V c _ _ _
  symmetry₂ := variableChartRelationLift_snd f hB d V c _ _ _
  c := PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  isLimit := pullbackIsPullback _ _
  t := variableChartRelationComp f hB d V c
  transitivity₁ := variableChartRelationLift_fst f hB d V c _ _ _
  transitivity₂ := variableChartRelationLift_snd f hB d V c _ _ _

/-- Swapping twice is the identity as an actual scheme morphism. -/
theorem variableChartRelationSwap_involutive :
    variableChartRelationSwap f hB d V c ≫ variableChartRelationSwap f hB d V c = 𝟙 _ := by
  have h₁ : variableChartRelationSwap f hB d V c ≫ variableChartRelationFst f hB d V c =
      variableChartRelationSnd f hB d V c := (variableChartEquivalenceRelation f hB d V c).symmetry₁
  have h₂ : variableChartRelationSwap f hB d V c ≫ variableChartRelationSnd f hB d V c =
      variableChartRelationFst f hB d V c := (variableChartEquivalenceRelation f hB d V c).symmetry₂
  apply variableChartRelation_hom_ext f hB d V c
  · rw [Category.assoc, h₁, h₂, Category.id_comp]
  · rw [Category.assoc, h₂, h₁, Category.id_comp]

end FLT.Mazur.HilbertChart
