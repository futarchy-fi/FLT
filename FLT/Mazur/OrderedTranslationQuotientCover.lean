/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationQuotientOpenImmersion
public import FLT.Mazur.SmoothTranslationOrbitCover

/-!
# Actual full chart quotients openly cover the original locally ringed quotient

The fixed ordered translations provide open immersions from their full
locally ringed orbit quotients, and the original coverage proof applies to
their exact images. No affine or scheme structure is inferred from this cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)

/-- The actual locally ringed quotient of one full ordered translation relation. -/
def orderedTranslationQuotient (i : SmoothHilbertTranslationIndex) : LocallyRingedSpace :=
  invariantLocallyRingedSpace (variableChartEquivalenceRelation f hL i.2
    (smoothTranslationTest f i.1) (smoothTranslationClass f hL.2.1 i.1))

/-- The full ordered chart quotient maps into the original locally ringed quotient. -/
def orderedTranslationQuotientInclusion (i : SmoothHilbertTranslationIndex) :
    orderedTranslationQuotient f hL i ⟶
      invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL) :=
  smoothTranslationQuotientInclusion f hL i.2 (smoothTranslationTest f i.1)
    (smoothTranslationClass f hL.2.1 i.1)

/-- Every ordered chart quotient inclusion is an actual open immersion. -/
instance orderedTranslationQuotientInclusion_isOpenImmersion
    (i : SmoothHilbertTranslationIndex) :
    LocallyRingedSpace.IsOpenImmersion (orderedTranslationQuotientInclusion f hL i) :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
    (smoothTranslationQuotientInclusion f hL i.2 (smoothTranslationTest f i.1)
      (smoothTranslationClass f hL.2.1 i.1)))

/-- The image is the previously proved ordered translation neighborhood. -/
theorem orderedTranslationQuotientInclusion_range (i : SmoothHilbertTranslationIndex) :
    Set.range (orderedTranslationQuotientInclusion f hL i).base =
      (orderedTranslationOrbitOpen f hL i :
        Set (Orbit (smoothHilbertEquivalenceRelation f hL))) :=
  smoothTranslationQuotientInclusion_range f hL i.2 (smoothTranslationTest f i.1)
    (smoothTranslationClass f hL.2.1 i.1)

/-- Every original quotient point lifts to one of the actual full chart quotients. -/
theorem orderedTranslationQuotientInclusion_covers
    (z : invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL)) :
    ∃ (i : SmoothHilbertTranslationIndex) (w : orderedTranslationQuotient f hL i),
      (orderedTranslationQuotientInclusion f hL i).base w = z := by
  obtain ⟨i, hi⟩ := orderedTranslationOrbitOpen_covers f hL z
  obtain ⟨w, hw⟩ :=
    (Set.ext_iff.mp (orderedTranslationQuotientInclusion_range f hL i) z).mpr hi
  exact ⟨i, w, hw⟩

end FLT.Mazur.HilbertChart
