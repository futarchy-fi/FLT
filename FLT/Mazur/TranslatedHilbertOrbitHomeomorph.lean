/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertOrbitFibers

/-!
# Translated Hilbert charts are the actual quotient opens topologically

The source-chart orbit map and parameter map are open quotient maps with
identical fibers. Their descended maps are inverse homeomorphisms. The
identification of structure sheaves is a separate remaining construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- The original chart cover is a continuous map of its actual scheme carriers. -/
def translatedParameterContinuous :
    C((translatedSourceIntersection f hL i).left, (acyclicHilbertTest f i.1).left) :=
  ⟨(translatedSourceParameter f hL i).left, (translatedSourceParameter f hL i).left.continuous⟩

/-- The smooth surjective parameter map has the actual quotient topology. -/
theorem translatedParameter_isOpenQuotientMap :
    IsOpenQuotientMap (translatedParameterContinuous f hL i) :=
  ⟨(translatedSourceParameter f hL i).left.surjective,
    (translatedParameterContinuous f hL i).continuous,
    (translatedSourceParameter f hL i).left.isOpenMap⟩

/-- Restricting the original orbit map to this invariant open remains an open quotient map. -/
theorem translatedSourceOrbitMap_isOpenQuotientMap :
    IsOpenQuotientMap (translatedSourceOrbitMap f hL i) := by
  refine ⟨translatedSourceOrbitMap_surjective f hL i,
    (translatedSourceOrbitMap f hL i).continuous, ?_⟩
  exact ((projection_isOpenMap (smoothHilbertEquivalenceRelation f hL)
    (smoothHilbertRelationSnd f hL).left.isOpenMap).comp
      (translatedSourceInclusion f hL i).left.isOpenMap).codRestrict _

/-- Descend the actual chart parameter along the source orbit map. -/
def translatedOrbitToChart :
    C(translatedOrbitOpen f hL i, (acyclicHilbertTest f i.1).left) :=
  (translatedSourceOrbitMap_isOpenQuotientMap f hL i).isQuotientMap.lift
    (translatedParameterContinuous f hL i)
    (fun {_ _} h ↦ (translatedSourceOrbitMap_eq_iff f hL i _ _).mp h)

/-- Descend the original orbit map along the actual smooth chart cover. -/
def translatedChartToOrbit :
    C((acyclicHilbertTest f i.1).left, translatedOrbitOpen f hL i) :=
  (translatedParameter_isOpenQuotientMap f hL i).isQuotientMap.lift
    (translatedSourceOrbitMap f hL i)
    (fun {_ _} h ↦ (translatedSourceOrbitMap_eq_iff f hL i _ _).mpr h)

/-- The descended chart parameter retains the original source coordinates. -/
theorem translatedOrbitToChart_source (x : (translatedSourceIntersection f hL i).left) :
    translatedOrbitToChart f hL i (translatedSourceOrbitMap f hL i x) =
      (translatedSourceParameter f hL i).left x :=
  congrArg (fun k : C(_, _) ↦ k x)
    ((translatedSourceOrbitMap_isOpenQuotientMap f hL i).isQuotientMap.lift_comp
      (translatedParameterContinuous f hL i)
      (fun {_ _} h ↦ (translatedSourceOrbitMap_eq_iff f hL i _ _).mp h))

/-- The descended chart-to-orbit map retains the actual source orbit. -/
theorem translatedChartToOrbit_parameter (x : (translatedSourceIntersection f hL i).left) :
    translatedChartToOrbit f hL i ((translatedSourceParameter f hL i).left x) =
      translatedSourceOrbitMap f hL i x :=
  congrArg (fun k : C(_, _) ↦ k x)
    ((translatedParameter_isOpenQuotientMap f hL i).isQuotientMap.lift_comp
      (translatedSourceOrbitMap f hL i)
      (fun {_ _} h ↦ (translatedSourceOrbitMap_eq_iff f hL i _ _).mpr h))

/-- The actual parameter scheme is homeomorphic to its descended quotient open. -/
def translatedOrbitChartHomeomorph :
    translatedOrbitOpen f hL i ≃ₜ (acyclicHilbertTest f i.1).left where
  toFun := translatedOrbitToChart f hL i
  invFun := translatedChartToOrbit f hL i
  left_inv z := by
    obtain ⟨x, rfl⟩ := translatedSourceOrbitMap_surjective f hL i z
    rw [translatedOrbitToChart_source, translatedChartToOrbit_parameter]
  right_inv z := by
    obtain ⟨x, rfl⟩ := (translatedSourceParameter f hL i).left.surjective z
    rw [translatedChartToOrbit_parameter, translatedOrbitToChart_source]
  continuous_toFun := (translatedOrbitToChart f hL i).continuous
  continuous_invFun := (translatedChartToOrbit f hL i).continuous

end FLT.Mazur.HilbertChart
