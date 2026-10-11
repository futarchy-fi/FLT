/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothHilbertGeometricCoverage
public import FLT.Mazur.GeometricPointCoverCriterion

/-!
# Actual smooth covering families of original Picard tests

Every original section has a countable jointly surjective family of smooth
represented chart intersections. The covering maps and chart maps retain the
original section, and constitute an actual fppf cover of its original test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- Every geometric point of the original test lifts to one actual chart intersection. -/
theorem smoothHilbertOverlap_geometric_lift
    {k : Type} [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T.left) :
    ∃ (i : SmoothHilbertTranslationIndex)
      (q : Spec (.of k) ⟶ (smoothHilbertOverlap f hB i T s).left),
      q ≫ (smoothHilbertOverlapToTest f hB i T s).left = p := by
  let b : Over.mk (p ≫ T.hom) ⟶ T := Over.homMk p
  obtain ⟨i, a, ha⟩ := exists_smoothHilbert_geometric_lift f hB (p ≫ T.hom)
    ((relativeFppfSheaf f).obj.map b.op s)
  obtain ⟨q, hq, _⟩ := variableHilbertOverlap_lift f i.2 hB
    (smoothTranslationTest f i.1) (smoothTranslationClass f hB.2.1 i.1) T s b a ha
  exact ⟨i, q.left, congrArg (fun z ↦ z.left) hq.1⟩

/-- Joint coverage is proved for every original test point, including nonclosed points. -/
theorem smoothHilbertOverlap_covers (x : T.left) :
    ∃ (i : SmoothHilbertTranslationIndex) (y : (smoothHilbertOverlap f hB i T s).left),
      (smoothHilbertOverlapToTest f hB i T s).left y = x :=
  GeometricPointCoverCriterion.covers _
    (fun _ _ _ p ↦ smoothHilbertOverlap_geometric_lift f hB T s p) x

/-- The constructed countable family is an actual fppf cover of the original test. -/
def smoothHilbertTestCover : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation)
    SmoothHilbertTranslationIndex (fun i ↦ (smoothHilbertOverlap f hB i T s).left)
    (fun i ↦ (smoothHilbertOverlapToTest f hB i T s).left)
    (smoothHilbertOverlap_covers f hB T s) (fun _ ↦ ⟨inferInstance, inferInstance⟩)

/-- Each member of this actual fppf family is smooth over the original test. -/
instance smoothHilbertTestCover_smooth (i : SmoothHilbertTranslationIndex) :
    Smooth ((smoothHilbertTestCover f hB T s).f i) :=
  smoothHilbertOverlapToTest_smooth f hB i T s

/-- The represented intersections generate an fppf covering sieve on the original test. -/
theorem smoothHilbertOverlap_covering :
    Sieve.ofArrows (fun i ↦ smoothHilbertOverlap f hB i T s)
      (fun i ↦ smoothHilbertOverlapToTest f hB i T s) ∈
      (Scheme.fppfTopology.over (Spec (.of R))) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck (smoothHilbertTestCover f hB T s).mem₀

end FLT.Mazur.HilbertChart
