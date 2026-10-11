/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationOrbitOpen

/-!
# Smooth translation neighborhoods cover the original quotient

The fixed ordered translation family supplies actual open neighborhoods of
every original orbit. Coverage follows from the proved geometric lifting
theorem on the original source, with no supplied coverage hypothesis.
These are quotient neighborhoods; their scheme effectivity still requires
descent of the smooth chart relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit OrderedCurvePower
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)

/-- The original quotient neighborhood of one fixed smooth ordered translation. -/
def orderedTranslationOrbitOpen (i : SmoothHilbertTranslationIndex) :
    Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) :=
  smoothTranslationOrbitOpen f hL i.2 (smoothTranslationTest f i.1)
    (smoothTranslationClass f hL.2.1 i.1)

/-- Each source point lies above one of the constructed smooth translation neighborhoods. -/
theorem orderedTranslationOrbitOpen_source_covers (x : (smoothHilbertSource f).left) :
    ∃ i, projection (smoothHilbertEquivalenceRelation f hL) x ∈
      orderedTranslationOrbitOpen f hL i := by
  obtain ⟨i, y, hy⟩ := smoothHilbertOverlap_covers f hL (smoothHilbertSource f)
    (smoothHilbertSourceSection f hL) x
  refine ⟨i, (mem_smoothTranslationOrbitOpen_iff f hL i.2 _ _ x).mpr ?_⟩
  exact ⟨y, hy⟩

/-- Every actual orbit has a neighborhood from the fixed countable smooth family. -/
theorem orderedTranslationOrbitOpen_covers (z : Orbit (smoothHilbertEquivalenceRelation f hL)) :
    ∃ i, z ∈ orderedTranslationOrbitOpen f hL i := by
  obtain ⟨x, rfl⟩ := projection_surjective (smoothHilbertEquivalenceRelation f hL) z
  exact orderedTranslationOrbitOpen_source_covers f hL x

/-- The constructed smooth translation neighborhoods cover the whole original quotient. -/
theorem orderedTranslationOrbitOpen_iSup :
    (⨆ i, orderedTranslationOrbitOpen f hL i) = ⊤ := by
  apply top_unique
  intro z _
  exact Opens.mem_iSup.mpr (orderedTranslationOrbitOpen_covers f hL z)

/-- Any original quotient neighborhood is covered by intersections with these actual opens. -/
theorem orderedTranslationOrbitOpen_refine
    (W : Opens (Orbit (smoothHilbertEquivalenceRelation f hL))) :
    (⨆ i, W ⊓ orderedTranslationOrbitOpen f hL i) = W := by
  apply le_antisymm
  · exact iSup_le fun _ ↦ inf_le_left
  · intro z hz
    obtain ⟨i, hi⟩ := orderedTranslationOrbitOpen_covers f hL z
    exact Opens.mem_iSup.mpr ⟨i, hz, hi⟩

end FLT.Mazur.HilbertChart
