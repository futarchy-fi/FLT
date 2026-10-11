/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationInvariantOpenDomains

/-!
# Functorial domains for the smooth translation comparison

The previously constructed full-chart opens are precisely inverse images under
the actual map from the chart orbit space to the original orbit space.
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
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The chart orbit map followed by the original quotient neighborhood inclusion. -/
def smoothTranslationChartOrbitMap :
    space (variableChartEquivalenceRelation f hL d V c) ⟶
      space (smoothHilbertEquivalenceRelation f hL) :=
  TopCat.ofHom ⟨fun z ↦ (smoothTranslationChartOrbitToOpen f hL d V c z).val,
    continuous_subtype_val.comp (smoothTranslationChartOrbitToOpen f hL d V c).continuous⟩

/-- The map of actual orbit spaces retains each original parameter point. -/
theorem smoothTranslationChartOrbitMap_projection (x : (variableHilbertTest f d V).left) :
    smoothTranslationChartOrbitMap f hL d V c
      (projection (variableChartEquivalenceRelation f hL d V c) x) =
        (smoothTranslationChartToOrbit f hL d V c x).val := by
  exact congrArg Subtype.val (smoothTranslationChartOrbitToOpen_projection f hL d V c x)

/-- The full-chart domain is the genuine inverse image of the original quotient open. -/
theorem smoothTranslationFullChartOrbitOpen_eq_preimage
    (O : TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL))) :
    smoothTranslationFullChartOrbitOpen f hL d V c O =
      (TopologicalSpace.Opens.map (smoothTranslationChartOrbitMap f hL d V c)).obj O := by
  apply (opensOrderIso (variableChartEquivalenceRelation f hL d V c)).injective
  apply Subtype.ext
  change (pullOpen _ (smoothTranslationFullChartOrbitOpen f hL d V c O)).val =
    (pullOpen _ _).val
  rw [smoothTranslationFullChartOrbitOpen_pull]
  ext x
  change (smoothTranslationChartToOrbit f hL d V c x).val ∈ O ↔
    smoothTranslationChartOrbitMap f hL d V c
      (projection (variableChartEquivalenceRelation f hL d V c) x) ∈ O
  rw [smoothTranslationChartOrbitMap_projection]

/-- Original open inclusions induce inclusions of their actual chart domains. -/
theorem smoothTranslationFullChartOrbitOpen_mono
    {O P : TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL))}
    (h : O ≤ P) :
    smoothTranslationFullChartOrbitOpen f hL d V c O ≤
      smoothTranslationFullChartOrbitOpen f hL d V c P := by
  rw [smoothTranslationFullChartOrbitOpen_eq_preimage,
    smoothTranslationFullChartOrbitOpen_eq_preimage]
  exact (TopologicalSpace.Opens.map (smoothTranslationChartOrbitMap f hL d V c)).map
    (homOfLE h) |>.le

/-- Parameter domains preserve inclusions of original quotient opens. -/
theorem smoothTranslationParameterOpen_mono
    {O P : TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL))}
    (h : O ≤ P) :
    smoothTranslationParameterOpen f hL d V c O ≤
      smoothTranslationParameterOpen f hL d V c P := fun _ hx ↦ h hx

/-- The full-chart opens, with their proved restriction maps, form a functor. -/
def smoothTranslationFullChartOpenFunctor :
    TopologicalSpace.Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) ⥤
      TopologicalSpace.Opens (Orbit (variableChartEquivalenceRelation f hL d V c)) where
  obj := smoothTranslationFullChartOrbitOpen f hL d V c
  map i := homOfLE (smoothTranslationFullChartOrbitOpen_mono f hL d V c i.le)

end FLT.Mazur.HilbertChart
