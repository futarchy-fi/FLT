/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantAffineComparison
public import FLT.Mazur.TranslatedHilbertInvariantStructureSheaf

/-!
# Actual locally ringed translated quotient charts

The existing orbit-chart homeomorphism and the proved natural invariant-sheaf
comparison give a locally ringed isomorphism with the actual parameter scheme.
This identifies each constructed chart, without claiming that these charts
cover the entire quotient over the arbitrary original base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- The actual invariant quotient open is the parameter scheme as a ringed space. -/
def translatedOrbitChartRingedIso :
    (invariantOpenSpace (smoothHilbertEquivalenceRelation f hL)
      (translatedOrbitOpen f hL i)).toSheafedSpace ≅
        (acyclicHilbertTest f i.1).left.toSheafedSpace :=
  SheafedSpace.isoMk (PresheafedSpace.isoOfComponents
    (TopCat.isoOfHomeo (translatedOrbitChartHomeomorph f hL i))
    (translatedChartInvariantStructureIso f hL i))

/-- The original quotient chart homeomorphism upgrades to an actual locally ringed isomorphism. -/
def translatedOrbitChartLocallyRingedIso :
    invariantOpenSpace (smoothHilbertEquivalenceRelation f hL)
      (translatedOrbitOpen f hL i) ≅ (acyclicHilbertTest f i.1).left.toLocallyRingedSpace :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (translatedOrbitChartRingedIso f hL i)

/-- The locally ringed chart isomorphism retains the original orbit-to-parameter map. -/
theorem translatedOrbitChartLocallyRingedIso_base :
    (translatedOrbitChartLocallyRingedIso f hL i).hom.base =
      TopCat.ofHom (translatedOrbitToChart f hL i) := rfl

/-- Its inverse retains the original parameter-to-orbit map. -/
theorem translatedOrbitChartLocallyRingedIso_inv_base :
    (translatedOrbitChartLocallyRingedIso f hL i).inv.base =
      TopCat.ofHom (translatedChartToOrbit f hL i) := rfl

/-- On original source points, the locally ringed chart retains the actual parameter. -/
theorem translatedOrbitChartLocallyRingedIso_source
    (x : (translatedSourceIntersection f hL i).left) :
    (translatedOrbitChartLocallyRingedIso f hL i).hom.base
      (translatedSourceOrbitMap f hL i x) = (translatedSourceParameter f hL i).left x :=
  translatedOrbitToChart_source f hL i x

end FLT.Mazur.HilbertChart
