/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothHilbertIntersectionLift

/-!
# The full original presheaf pullback of the assembled Hilbert source

The actual disjoint union of chart intersections represents the fiber product
on every original test, including maps spanning several source components.
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
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The assembled intersection represents the complete original presheaf fiber product. -/
theorem smoothHilbertSourceMap_isPullback :
    IsPullback (uliftYoneda.{1}.map (smoothHilbertIntersectionToSource f hB T s))
      (uliftYoneda.{1}.map (smoothHilbertIntersectionToTest f hB T s))
      (smoothHilbertSourceMap f hB) (uliftYonedaEquiv.symm s) := by
  apply IsPullback.of_forall_isPullback_app
  intro U
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro q
    change (relativeFppfSheaf f).obj.map
      (q.down ≫ smoothHilbertIntersectionToSource f hB T s).op
        (smoothHilbertSourceSection f hB) =
          (relativeFppfSheaf f).obj.map
            (q.down ≫ smoothHilbertIntersectionToTest f hB T s).op s
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rw [smoothHilbertIntersectionSource_class]
  · intro q r hqr
    apply ULift.ext
    exact smoothHilbertIntersection_hom_ext f hB T s
      (congrArg ULift.down hqr.1) (congrArg ULift.down hqr.2)
  · intro k b hkb
    obtain ⟨q, hq, _⟩ := smoothHilbertIntersection_lift f hB T s k.down b.down hkb
    exact ⟨ULift.up q, ULift.ext hq.1, ULift.ext hq.2⟩

end FLT.Mazur.HilbertChart
