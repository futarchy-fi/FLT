/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertRefinedModelKernel
public import FLT.Mazur.VariableHilbertDescendedGeometry

/-!
# Full fppf model existence is invariant under translation refinement

For each actual target scheme, composing or descending the source projection
transfers full effective fppf presentations in both directions. The theorem
is an equivalence of existence statements; it does not assert either side
without a constructed model.
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
  [LocallyOfFinitePresentation V.hom]
  [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "g" => baseMarkedChartChange f b d
local notation "P" => variableChartRelationFst f hL d V c
local notation "Q" => variableChartRelationSnd f hL d V c
local notation "P₁" => variableChartRelationFst f hL d W cW
local notation "Q₁" => variableChartRelationSnd f hL d W cW

/-- The same target admits a full fppf model before refinement exactly when it does afterward. -/
theorem fullFppfModel_refinement_iff (Z : Over (Spec (.of R))) :
    (∃ π : variableHilbertTest f d V ⟶ Z,
      Flat π.left ∧ LocallyOfFinitePresentation π.left ∧ Surjective π.left ∧
        IsPullback P Q π π) ↔
    ∃ π : variableHilbertTest f d W ⟶ Z,
      Flat π.left ∧ LocallyOfFinitePresentation π.left ∧ Surjective π.left ∧
        IsPullback P₁ Q₁ π π := by
  constructor
  · rintro ⟨π, hf, hl, hs, H⟩
    refine ⟨g ≫ π, ?_, ?_, ?_, refinedModelProjection_isPullback f hL d b c π H⟩
    · change Flat ((g).left ≫ π.left)
      infer_instance
    · change LocallyOfFinitePresentation ((g).left ≫ π.left)
      infer_instance
    · change Surjective ((g).left ≫ π.left)
      infer_instance
  · rintro ⟨π, hf, hl, hs, H⟩
    exact ⟨descendedProjection f hL d b c π H.w, inferInstance,
      descendedProjection_locallyOfFinitePresentation f hL d b c π H, inferInstance,
      descendedProjection_isPullback f hL d b c π H⟩

/-- Constructing the model after refinement suffices, with no original projection input. -/
theorem exists_fullFppfModel_iff :
    (∃ (Z : Over (Spec (.of R))) (π : variableHilbertTest f d V ⟶ Z),
      Flat π.left ∧ LocallyOfFinitePresentation π.left ∧ Surjective π.left ∧
        IsPullback P Q π π) ↔
    ∃ (Z : Over (Spec (.of R))) (π : variableHilbertTest f d W ⟶ Z),
      Flat π.left ∧ LocallyOfFinitePresentation π.left ∧ Surjective π.left ∧
        IsPullback P₁ Q₁ π π :=
  exists_congr fun Z ↦ fullFppfModel_refinement_iff f hL d b c Z

omit [LocallyOfFinitePresentation V.hom] in
/-- Composing an original model and descending again recovers the original scheme projection. -/
theorem descend_refinedModelProjection {Z : Over (Spec (.of R))}
    (π : variableHilbertTest f d V ⟶ Z)
    (H : IsPullback (variableChartRelationFst f hL d V c)
      (variableChartRelationSnd f hL d V c) π π) :
    descendedProjection f hL d b c (g ≫ π)
      (refinedModelProjection_condition f hL d b c π H) = π :=
  (descendedProjection_unique f hL d b c (g ≫ π)
    (refinedModelProjection_condition f hL d b c π H) π rfl).symm

end FLT.Mazur.VariableHilbertFppfRefinement
