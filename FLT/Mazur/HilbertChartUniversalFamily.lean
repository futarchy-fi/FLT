/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartEvaluationSurjective
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# The finite locally free family over a Hilbert chart

The spectrum of the actual chart algebra is finite, flat and finitely presented
of rank `d` over the chart. No nontriviality assumption on the base ring is needed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.HilbertChart

universe u

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient-ring instance for nested tensor inference. -/
local instance familyCoefficientsRing : CommRing (Coefficients R I d) := inferInstance

/-- Cache the chart-ring instance for nested tensor inference. -/
local instance familyChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- The actual parameter scheme for the prescribed-basis chart. -/
abbrev chartScheme : Scheme := Spec (CommRingCat.of (ChartRing R I d w))

/-- The actual scheme underlying the universal finite family on the chart. -/
abbrev chartFamily : Scheme := Spec (CommRingCat.of (ChartAlgebra R I d w))

/-- The structure map of the actual universal chart family. -/
def chartFamilyMap : chartFamily R I d w ⟶ chartScheme R I d w :=
  Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R I d w) (ChartAlgebra R I d w)))

instance : IsFinite (chartFamilyMap R I d w) := by
  rw [chartFamilyMap, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.finite_algebraMap]
  infer_instance

instance : Flat (chartFamilyMap R I d w) := by
  rw [chartFamilyMap, Flat.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff]
  infer_instance

instance : LocallyOfFinitePresentation (chartFamilyMap R I d w) := by
  let _ : Module.FinitePresentation (ChartRing R I d w) (ChartAlgebra R I d w) :=
    Module.finitePresentation_of_projective _ _
  rw [chartFamilyMap, LocallyOfFinitePresentation.SpecMap_iff,
    CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
  infer_instance

/-- Every actual fiber has the prescribed rank, including the empty rank-zero family. -/
theorem chartFamilyMap_finrank (p : chartScheme R I d w) :
    (chartFamilyMap R I d w).finrank p = d := by
  let _ : Nontrivial (ChartRing R I d w) := PrimeSpectrum.nontrivial p
  calc
    _ = Module.rankAtStalk (ChartAlgebra R I d w) p :=
      Scheme.Hom.finrank_SpecMap_algebraMap (ChartRing R I d w) (ChartAlgebra R I d w) p
    _ = Module.finrank (ChartRing R I d w) (ChartAlgebra R I d w) :=
      congrFun Module.rankAtStalk_eq_finrank_of_free p
    _ = d := (Module.finrank_eq_card_basis (chartBasis R I d w)).trans (Fintype.card_fin d)

end FLT.Mazur.HilbertChart
