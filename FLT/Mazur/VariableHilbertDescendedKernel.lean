/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertRefinedProjection
public import FLT.Mazur.RelativeFppfPairCover
public import FLT.Mazur.RelativePicardFppfSingletonDescent

/-!
# The descended projection has the full original Hilbert kernel pair

An actual kernel-pair presentation after fppf translation refinement descends
on both independent endpoints. Original Picard sheaf separatedness detects
equality after the constructed common cover. This uses no compatibility of
the translating section on the translation base kernel pair.
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
  [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "g" => baseMarkedChartChange f b d
local notation "P" => variableChartRelationFst f hL d V c
local notation "Q" => variableChartRelationSnd f hL d V c
local notation "P₁" => variableChartRelationFst f hL d W cW
local notation "Q₁" => variableChartRelationSnd f hL d W cW
variable {Z : Over (Spec (.of R))} (π : variableHilbertTest f d W ⟶ Z)
  (H : IsPullback
    (variableChartRelationFst f hL d W ((relativeFppfSheaf f).obj.map b.op c))
    (variableChartRelationSnd f hL d W ((relativeFppfSheaf f).obj.map b.op c)) π π)
local notation "D" => descendedProjection f hL d b c π H.w

omit [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left] in
include H in
/-- Equal refined projection values imply equality of the original refined Picard classes. -/
theorem refinedProjection_class {T : Over (Spec (.of R))}
    (a a' : T ⟶ variableHilbertTest f d W) (ha : a ≫ π = a' ≫ π) :
    (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d W cW) =
      (relativeFppfSheaf f).obj.map a'.op (variableChartSection f hL d W cW) := by
  have hc := congrArg ((relativeFppfSheaf f).obj.map (H.lift a a' ha).op)
    (variableChartRelation_class f hL d W cW)
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    H.lift_fst, H.lift_snd] using hc

/-- The original full equal-class relation is exactly equality under the descended projection. -/
theorem descendedProjection_eq_iff {T : Over (Spec (.of R))}
    (a a' : T ⟶ variableHilbertTest f d V) :
    a ≫ D = a' ≫ D ↔
      (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) =
        (relativeFppfSheaf f).obj.map a'.op (variableChartSection f hL d V c) := by
  constructor
  · intro ha
    let t := RelativeFppfPairCover.cover g a a'
    let u := RelativeFppfPairCover.fst g a a'
    let v := RelativeFppfPairCover.snd g a a'
    have hu : u ≫ g = t ≫ a := RelativeFppfPairCover.fst_map g a a'
    have hv : v ≫ g = t ≫ a' := RelativeFppfPairCover.snd_map g a a'
    have huv : u ≫ π = v ≫ π := by
      rw [← descendedProjection_source f hL d b c π H.w,
        ← Category.assoc, hu, Category.assoc, ha, ← Category.assoc, ← hv, Category.assoc]
    apply relativePicardFppf_singleton_injective f t
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rw [← hu, ← hv, class_map, class_map]
    exact refinedProjection_class f hL d b c π H u v huv
  · intro ha
    let r := variableChartRelationLift f hL d V c a a' ha
    have hr : r ≫ P = a := variableChartRelationLift_fst f hL d V c a a' ha
    have hr' : r ≫ Q = a' := variableChartRelationLift_snd f hL d V c a a' ha
    rw [← hr, ← hr', Category.assoc, Category.assoc, descendedProjection_condition]

/-- The original full relation represents the kernel of the actual descended scheme map. -/
theorem descendedProjection_isPullback : IsPullback P Q D D := by
  let lift (z : PullbackCone D D) :=
    variableChartRelation_lift f hL d V c z.fst z.snd
      ((descendedProjection_eq_iff f hL d b c π H z.fst z.snd).mp z.condition)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (descendedProjection_condition f hL d b c π H.w) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2)
    (fun z r h₁ h₂ ↦ (lift z).choose_spec.2 r ⟨h₁, h₂⟩))

end FLT.Mazur.VariableHilbertFppfRefinement
