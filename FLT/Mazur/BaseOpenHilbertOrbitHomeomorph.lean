/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseOpenHilbertOrbitFibers

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
  (d : ℕ) (V : Over (Spec (.of R))) [IsOpenImmersion V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The original chart cover is a continuous map of its actual scheme carriers. -/
def baseOpenParameterContinuous :
    C((variableSourceIntersection f hL d V c).left, (variableHilbertTest f d V).left) :=
  ⟨(variableSourceParameter f hL d V c).left, (variableSourceParameter f hL d V c).left.continuous⟩

omit [IsOpenImmersion V.hom] in
/-- The smooth surjective parameter map has the actual quotient topology. -/
theorem baseOpenParameter_isOpenQuotientMap :
    IsOpenQuotientMap (baseOpenParameterContinuous f hL d V c) :=
  ⟨(variableSourceParameter f hL d V c).left.surjective,
    (baseOpenParameterContinuous f hL d V c).continuous,
    (variableSourceParameter f hL d V c).left.isOpenMap⟩

/-- Restricting the original orbit map to this invariant open remains an open quotient map. -/
theorem baseOpenSourceOrbitMap_isOpenQuotientMap :
    IsOpenQuotientMap (baseOpenSourceOrbitMap f hL d V c) := by
  refine ⟨baseOpenSourceOrbitMap_surjective f hL d V c,
    (baseOpenSourceOrbitMap f hL d V c).continuous, ?_⟩
  exact ((projection_isOpenMap (smoothHilbertEquivalenceRelation f hL)
    (smoothHilbertRelationSnd f hL).left.isOpenMap).comp
      (variableSourceInclusion f hL d V c).left.isOpenMap).codRestrict _

/-- Descend the actual chart parameter along the source orbit map. -/
def baseOpenOrbitToChart :
    C(baseOpenOrbitOpen f hL d V c, (variableHilbertTest f d V).left) :=
  (baseOpenSourceOrbitMap_isOpenQuotientMap f hL d V c).isQuotientMap.lift
    (baseOpenParameterContinuous f hL d V c)
    (fun {_ _} h ↦ (baseOpenSourceOrbitMap_eq_iff f hL d V c _ _).mp h)

/-- Descend the original orbit map along the actual smooth chart cover. -/
def baseOpenChartToOrbit :
    C((variableHilbertTest f d V).left, baseOpenOrbitOpen f hL d V c) :=
  (baseOpenParameter_isOpenQuotientMap f hL d V c).isQuotientMap.lift
    (baseOpenSourceOrbitMap f hL d V c)
    (fun {_ _} h ↦ (baseOpenSourceOrbitMap_eq_iff f hL d V c _ _).mpr h)

/-- The descended chart parameter retains the original source coordinates. -/
theorem baseOpenOrbitToChart_source (x : (variableSourceIntersection f hL d V c).left) :
    baseOpenOrbitToChart f hL d V c (baseOpenSourceOrbitMap f hL d V c x) =
      (variableSourceParameter f hL d V c).left x :=
  congrArg (fun k : C(_, _) ↦ k x)
    ((baseOpenSourceOrbitMap_isOpenQuotientMap f hL d V c).isQuotientMap.lift_comp
      (baseOpenParameterContinuous f hL d V c)
      (fun {_ _} h ↦ (baseOpenSourceOrbitMap_eq_iff f hL d V c _ _).mp h))

/-- The descended chart-to-orbit map retains the actual source orbit. -/
theorem baseOpenChartToOrbit_parameter (x : (variableSourceIntersection f hL d V c).left) :
    baseOpenChartToOrbit f hL d V c ((variableSourceParameter f hL d V c).left x) =
      baseOpenSourceOrbitMap f hL d V c x :=
  congrArg (fun k : C(_, _) ↦ k x)
    ((baseOpenParameter_isOpenQuotientMap f hL d V c).isQuotientMap.lift_comp
      (baseOpenSourceOrbitMap f hL d V c)
      (fun {_ _} h ↦ (baseOpenSourceOrbitMap_eq_iff f hL d V c _ _).mpr h))

/-- The actual parameter scheme is homeomorphic to its descended quotient open. -/
def baseOpenOrbitChartHomeomorph :
    baseOpenOrbitOpen f hL d V c ≃ₜ (variableHilbertTest f d V).left where
  toFun := baseOpenOrbitToChart f hL d V c
  invFun := baseOpenChartToOrbit f hL d V c
  left_inv z := by
    obtain ⟨x, rfl⟩ := baseOpenSourceOrbitMap_surjective f hL d V c z
    rw [baseOpenOrbitToChart_source, baseOpenChartToOrbit_parameter]
  right_inv z := by
    obtain ⟨x, rfl⟩ := (variableSourceParameter f hL d V c).left.surjective z
    rw [baseOpenChartToOrbit_parameter, baseOpenOrbitToChart_source]
  continuous_toFun := (baseOpenOrbitToChart f hL d V c).continuous
  continuous_invFun := (baseOpenChartToOrbit f hL d V c).continuous

end FLT.Mazur.HilbertChart
