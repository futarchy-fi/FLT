/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertDescendedKernel
public import FLT.Mazur.VariableHilbertEffectivePicardImage

/-!
# A refined model retains exactly the original Picard chart image

The model's section pulls back along the constructed ORIGINAL projection to
the original universal class. Its image on every original test consists
exactly of sections fppf-locally represented by the original source, without
requiring the original translating section to descend to the coefficient base.
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
  {Z : Over (Spec (.of R))} (π : variableHilbertTest f d W ⟶ Z)
  (H : IsPullback
    (variableChartRelationFst f hL d W ((relativeFppfSheaf f).obj.map b.op c))
    (variableChartRelationSnd f hL d W ((relativeFppfSheaf f).obj.map b.op c)) π π)
  [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "g" => baseMarkedChartChange f b d
local notation "sZ" => effectivePicardSection f hL d W cW π H
local notation "s" => variableChartSection f hL d V c

/-- The refined model's Picard section pulls back to the exact original universal section. -/
theorem descendedProjection_picard :
    (relativeFppfSheaf f).obj.map (descendedProjection f hL d b c π H.w).op sZ = s := by
  apply relativePicardFppf_singleton_injective f g
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    descendedProjection_source, effectivePicardSection_source]
  have hg := class_map f hL d b c (𝟙 _)
  rw [Category.id_comp, op_id, (relativeFppfSheaf f).obj.map_id] at hg
  exact hg.symm

/-- The refined model represents the fppf-local image of the ORIGINAL parameter source. -/
theorem descendedPicardImage_iff {T : Over (Spec (.of R))}
    (z : (relativeFppfSheaf f).obj.obj (op T)) :
    (∃ k : T ⟶ Z, (relativeFppfSheaf f).obj.map k.op sZ = z) ↔
      ∃ (T' : Over (Spec (.of R))) (t : T' ⟶ T)
        (a : T' ⟶ variableHilbertTest f d V),
        Flat t.left ∧ LocallyOfFinitePresentation t.left ∧ Surjective t.left ∧
          (relativeFppfSheaf f).obj.map t.op z = (relativeFppfSheaf f).obj.map a.op s := by
  constructor
  · intro hz
    obtain ⟨T', t, a, ht₁, ht₂, ht₃, ha⟩ :=
      (effectivePicardImage_iff f hL d W cW π H z).mp hz
    exact ⟨T', t, a ≫ g, ht₁, ht₂, ht₃, (class_map f hL d b c a).symm ▸ ha⟩
  · rintro ⟨T', t, a, ht₁, ht₂, ht₃, ha⟩
    let v := RelativeFppfPairCover.cover g a a
    let u := RelativeFppfPairCover.fst g a a
    have hu : u ≫ g = v ≫ a := RelativeFppfPairCover.fst_map g a a
    let _ : Flat (v ≫ t).left := by change Flat (v.left ≫ t.left); infer_instance
    let _ : LocallyOfFinitePresentation (v ≫ t).left := by
      change LocallyOfFinitePresentation (v.left ≫ t.left)
      infer_instance
    let _ : Surjective (v ≫ t).left := by change Surjective (v.left ≫ t.left); infer_instance
    have hz : (relativeFppfSheaf f).obj.map (v ≫ t).op z =
        (relativeFppfSheaf f).obj.map u.op (variableChartSection f hL d W cW) := by
      rw [← class_map, hu]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ha]
    exact (effectivePicardImage_existsUnique f hL d W cW π H (v ≫ t) u z hz).exists

end FLT.Mazur.VariableHilbertFppfRefinement
