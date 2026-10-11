/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantAffineComparison
public import FLT.Mazur.BaseOpenHilbertInvariantStructureSheaf

/-!
# Actual locally ringed base-local quotient charts

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
  (d : ℕ) (T₀ : Over (Spec (.of R))) [IsOpenImmersion T₀.hom]
  (c : (relativeFppfSheaf f).obj.obj (op T₀))

/-- The actual invariant quotient open is the parameter scheme as a ringed space. -/
def baseOpenOrbitChartRingedIso :
    (invariantOpenSpace (smoothHilbertEquivalenceRelation f hL)
      (baseOpenOrbitOpen f hL d T₀ c)).toSheafedSpace ≅
        (variableHilbertTest f d T₀).left.toSheafedSpace :=
  SheafedSpace.isoMk (PresheafedSpace.isoOfComponents
    (TopCat.isoOfHomeo (baseOpenOrbitChartHomeomorph f hL d T₀ c))
    (baseOpenChartInvariantStructureIso f hL d T₀ c))

/-- The original quotient chart homeomorphism upgrades to an actual locally ringed isomorphism. -/
def baseOpenOrbitChartLocallyRingedIso :
    invariantOpenSpace (smoothHilbertEquivalenceRelation f hL)
      (baseOpenOrbitOpen f hL d T₀ c) ≅ (variableHilbertTest f d T₀).left.toLocallyRingedSpace :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (baseOpenOrbitChartRingedIso f hL d T₀ c)

/-- The locally ringed chart isomorphism retains the original orbit-to-parameter map. -/
theorem baseOpenOrbitChartLocallyRingedIso_base :
    (baseOpenOrbitChartLocallyRingedIso f hL d T₀ c).hom.base =
      TopCat.ofHom (baseOpenOrbitToChart f hL d T₀ c) := rfl

/-- Its inverse retains the original parameter-to-orbit map. -/
theorem baseOpenOrbitChartLocallyRingedIso_inv_base :
    (baseOpenOrbitChartLocallyRingedIso f hL d T₀ c).inv.base =
      TopCat.ofHom (baseOpenChartToOrbit f hL d T₀ c) := rfl

/-- On original source points, the locally ringed chart retains the actual parameter. -/
theorem baseOpenOrbitChartLocallyRingedIso_source
    (x : (variableSourceIntersection f hL d T₀ c).left) :
    (baseOpenOrbitChartLocallyRingedIso f hL d T₀ c).hom.base
      (baseOpenSourceOrbitMap f hL d T₀ c x) = (variableSourceParameter f hL d T₀ c).left x :=
  baseOpenOrbitToChart_source f hL d T₀ c x

end FLT.Mazur.HilbertChart
