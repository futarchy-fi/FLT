/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothHilbertSourcePullback
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Representable smooth surjectivity of the single Hilbert source

The assembled map to the original Picard sheaf is representable by smooth
surjective morphisms. This is a presentation, not representability of its target.
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

/-- Every base change of the actual source map is represented and smooth surjective. -/
theorem smoothHilbertSourceMap_representablySmoothSurjective :
    (((@Smooth ⊓ @Surjective : MorphismProperty Scheme).inverseImage
      (Over.forget (Spec (.of R)))).relative uliftYoneda.{1})
        (smoothHilbertSourceMap f hB) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let s : (relativeFppfSheaf f).obj.obj (op T) := uliftYonedaEquiv g
  refine ⟨smoothHilbertIntersectionSource f hB T s,
    uliftYoneda.map (smoothHilbertIntersectionToSource f hB T s),
    smoothHilbertIntersectionToTest f hB T s, ?_, ?_⟩
  · simpa only [s, Equiv.symm_apply_apply] using smoothHilbertSourceMap_isPullback f hB T s
  · exact ⟨smoothHilbertIntersectionToTest_smooth f hB T s,
      smoothHilbertIntersectionToTest_surjective f hB T s⟩

/-- In particular, the source map is relatively representable on all original tests. -/
theorem smoothHilbertSourceMap_relativelyRepresentable :
    uliftYoneda.{1}.relativelyRepresentable (smoothHilbertSourceMap f hB) :=
  (smoothHilbertSourceMap_representablySmoothSurjective f hB).rep

/-- Smooth surjectivity holds for every represented pullback, independently of its choice. -/
theorem smoothHilbertSourceMap_pullback_smooth_surjective
    {T U : Over (Spec (.of R))}
    (g : uliftYoneda.{1}.obj T ⟶ (relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
    (a : uliftYoneda.{1}.obj U ⟶ uliftYoneda.{1}.obj (smoothHilbertSource f))
    (b : U ⟶ T)
    (h : IsPullback a (uliftYoneda.map b) (smoothHilbertSourceMap f hB) g) :
    Smooth b.left ∧ Surjective b.left :=
  (smoothHilbertSourceMap_representablySmoothSurjective f hB).property g a b h

end FLT.Mazur.HilbertChart
