/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothHilbertRelation
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# The internal equivalence relation of the smooth Hilbert presentation

Reflexivity, symmetry, and composition are constructed as actual scheme maps
from equality of the original Picard classes. No quotient scheme is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

/-- The unique actual relation map of two equal-class source morphisms. -/
def smoothHilbertRelationLift {T : Over (Spec (.of R))}
    (a b : T ⟶ smoothHilbertSource f)
    (h : (relativeFppfSheaf f).obj.map a.op (smoothHilbertSourceSection f hB) =
      (relativeFppfSheaf f).obj.map b.op (smoothHilbertSourceSection f hB)) :
    T ⟶ smoothHilbertRelation f hB :=
  (smoothHilbertRelation_lift f hB a b h).choose

/-- The first projection of the constructed relation map. -/
theorem smoothHilbertRelationLift_fst {T : Over (Spec (.of R))}
    (a b : T ⟶ smoothHilbertSource f) (h) :
    smoothHilbertRelationLift f hB a b h ≫ smoothHilbertRelationFst f hB = a :=
  (smoothHilbertRelation_lift f hB a b h).choose_spec.1.1

/-- The second projection of the constructed relation map. -/
theorem smoothHilbertRelationLift_snd {T : Over (Spec (.of R))}
    (a b : T ⟶ smoothHilbertSource f) (h) :
    smoothHilbertRelationLift f hB a b h ≫ smoothHilbertRelationSnd f hB = b :=
  (smoothHilbertRelation_lift f hB a b h).choose_spec.1.2

/-- The diagonal relation morphism is constructed from equality with itself. -/
def smoothHilbertRelationRefl : smoothHilbertSource f ⟶ smoothHilbertRelation f hB :=
  smoothHilbertRelationLift f hB (𝟙 _) (𝟙 _) rfl

/-- The inverse relation morphism exchanges the actual projections. -/
def smoothHilbertRelationSwap : smoothHilbertRelation f hB ⟶ smoothHilbertRelation f hB :=
  smoothHilbertRelationLift f hB (smoothHilbertRelationSnd f hB)
    (smoothHilbertRelationFst f hB) (smoothHilbertRelation_class f hB).symm

/-- Equality of original classes is transitive on the actual composable-pair scheme. -/
theorem smoothHilbertRelation_composable_class :
    (relativeFppfSheaf f).obj.map
      (pullback.fst (smoothHilbertRelationSnd f hB) (smoothHilbertRelationFst f hB) ≫
        smoothHilbertRelationFst f hB).op (smoothHilbertSourceSection f hB) =
    (relativeFppfSheaf f).obj.map
      (pullback.snd (smoothHilbertRelationSnd f hB) (smoothHilbertRelationFst f hB) ≫
        smoothHilbertRelationSnd f hB).op (smoothHilbertSourceSection f hB) := by
  calc
    _ = (relativeFppfSheaf f).obj.map
        (pullback.fst (smoothHilbertRelationSnd f hB) (smoothHilbertRelationFst f hB) ≫
          smoothHilbertRelationSnd f hB).op (smoothHilbertSourceSection f hB) := by
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      rw [smoothHilbertRelation_class]
    _ = (relativeFppfSheaf f).obj.map
        (pullback.snd (smoothHilbertRelationSnd f hB) (smoothHilbertRelationFst f hB) ≫
          smoothHilbertRelationFst f hB).op (smoothHilbertSourceSection f hB) := by
      rw [pullback.condition]
    _ = _ := by
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      rw [smoothHilbertRelation_class]

/-- Composition is an actual scheme morphism from the composable-pair pullback. -/
def smoothHilbertRelationComp :
    Limits.pullback (smoothHilbertRelationSnd f hB) (smoothHilbertRelationFst f hB) ⟶
      smoothHilbertRelation f hB :=
  smoothHilbertRelationLift f hB (pullback.fst _ _ ≫ smoothHilbertRelationFst f hB)
    (pullback.snd _ _ ≫ smoothHilbertRelationSnd f hB)
    (smoothHilbertRelation_composable_class f hB)

/-- The represented original equal-class relation is an internal equivalence relation. -/
def smoothHilbertEquivalenceRelation :
    CategoryTheory.EquivalenceRelation
      (smoothHilbertRelationFst f hB) (smoothHilbertRelationSnd f hB) where
  right_cancellation _ _ _ h₁ h₂ := smoothHilbertRelation_hom_ext f hB h₁ h₂
  r := smoothHilbertRelationRefl f hB
  reflexivity₁ := smoothHilbertRelationLift_fst f hB _ _ _
  reflexivity₂ := smoothHilbertRelationLift_snd f hB _ _ _
  s := smoothHilbertRelationSwap f hB
  symmetry₁ := smoothHilbertRelationLift_fst f hB _ _ _
  symmetry₂ := smoothHilbertRelationLift_snd f hB _ _ _
  c := PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  isLimit := pullbackIsPullback _ _
  t := smoothHilbertRelationComp f hB
  transitivity₁ := smoothHilbertRelationLift_fst f hB _ _ _
  transitivity₂ := smoothHilbertRelationLift_snd f hB _ _ _

/-- Swapping twice is the identity as an actual scheme morphism. -/
theorem smoothHilbertRelationSwap_involutive :
    smoothHilbertRelationSwap f hB ≫ smoothHilbertRelationSwap f hB = 𝟙 _ := by
  have h₁ : smoothHilbertRelationSwap f hB ≫ smoothHilbertRelationFst f hB =
      smoothHilbertRelationSnd f hB := (smoothHilbertEquivalenceRelation f hB).symmetry₁
  have h₂ : smoothHilbertRelationSwap f hB ≫ smoothHilbertRelationSnd f hB =
      smoothHilbertRelationFst f hB := (smoothHilbertEquivalenceRelation f hB).symmetry₂
  apply smoothHilbertRelation_hom_ext f hB
  · rw [Category.assoc, h₁, h₂, Category.id_comp]
  · rw [Category.assoc, h₂, h₁, Category.id_comp]

end FLT.Mazur.HilbertChart
