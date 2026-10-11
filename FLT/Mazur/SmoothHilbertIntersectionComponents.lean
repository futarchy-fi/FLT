/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCoproductPullCover
public import FLT.Mazur.SmoothHilbertIntersectionSource

/-!
# Components and uniqueness for the assembled Hilbert intersection

The inverse image of each source chart is its actual represented intersection.
The two assembled projections therefore distinguish arbitrary test morphisms.
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

/-- Every source component pulls back to its actual chart-test intersection. -/
theorem smoothHilbertIntersection_component_isPullback (i : SmoothHilbertTranslationIndex) :
    IsPullback (smoothHilbertOverlapToChart f hB i T s)
      (relativeCoproductArrow (fun j ↦ smoothHilbertOverlap f hB j T s) i)
      (smoothHilbertSourceArrow f i) (smoothHilbertIntersectionToSource f hB T s) :=
  relativeCoproductMap_component_isPullback
    (fun j ↦ smoothHilbertOverlap f hB j T s) (smoothHilbertTest f)
    (fun j ↦ smoothHilbertOverlapToChart f hB j T s) i

/-- Both assembled projections together determine every morphism into the intersection. -/
theorem smoothHilbertIntersection_hom_ext {U : Over (Spec (.of R))}
    {a b : U ⟶ smoothHilbertIntersectionSource f hB T s}
    (hc : a ≫ smoothHilbertIntersectionToSource f hB T s =
      b ≫ smoothHilbertIntersectionToSource f hB T s)
    (ht : a ≫ smoothHilbertIntersectionToTest f hB T s =
      b ≫ smoothHilbertIntersectionToTest f hB T s) : a = b := by
  let k := a ≫ smoothHilbertIntersectionToSource f hB T s
  apply relativeCoproductPull_hom_ext (smoothHilbertTest f) k
  intro i
  let v := relativeCoproductPullToDomain (smoothHilbertTest f) k i
  let c := relativeCoproductPullToComponent (smoothHilbertTest f) k i
  have ha : c ≫ smoothHilbertSourceArrow f i =
      (v ≫ a) ≫ smoothHilbertIntersectionToSource f hB T s := by
    rw [Category.assoc]
    exact
      (relativeCoproductPull_square (smoothHilbertTest f) k i).symm
  have hb : c ≫ smoothHilbertSourceArrow f i =
      (v ≫ b) ≫ smoothHilbertIntersectionToSource f hB T s := by
    rw [ha, Category.assoc, hc, ← Category.assoc]
  have H := smoothHilbertIntersection_component_isPullback f hB T s i
  obtain ⟨a', hac, hai⟩ := H.exists_lift c (v ≫ a) ha
  obtain ⟨b', hbc, hbi⟩ := H.exists_lift c (v ≫ b) hb
  have he : a' = b' := by
    apply variableHilbertOverlap_hom_ext f i.2 hB _ _ T s
    · calc
        a' ≫ smoothHilbertOverlapToTest f hB i T s =
            (v ≫ a) ≫ smoothHilbertIntersectionToTest f hB T s := by
          rw [← hai, Category.assoc, smoothHilbertIntersectionToTest_chart]
        _ = (v ≫ b) ≫ smoothHilbertIntersectionToTest f hB T s := by
          rw [Category.assoc, ht, ← Category.assoc]
        _ = b' ≫ smoothHilbertOverlapToTest f hB i T s := by
          rw [← hbi, Category.assoc, smoothHilbertIntersectionToTest_chart]
    · exact hac.trans hbc.symm
  exact hai.symm.trans ((congrArg (fun z ↦ z ≫
    relativeCoproductArrow (fun j ↦ smoothHilbertOverlap f hB j T s) i) he).trans hbi)

end FLT.Mazur.HilbertChart
