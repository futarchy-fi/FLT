/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConnectedIrreducibleNeighborhoods
public import FLT.Mazur.SmoothDimension
public import FLT.Mazur.StandardSmoothCurveLocalDomain

/-!
# Irreducibility of connected smooth field curves

Standard smooth charts over the original field admit smaller domain charts.
Their irreducible open images provide the neighborhoods that turn connectedness
into irreducibility. No global irreducibility hypothesis is imposed on a chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]

include f

/-- Every point of a smooth field curve has an irreducible open neighborhood. -/
theorem smoothCurve_irreducible_neighborhood (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IrreducibleSpace U := by
  obtain ⟨V, hV, hx, _, g, hg⟩ := exists_standardSmooth_affine_chart f 1 x
  let _ := g.toAlgebra
  let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(X, V) := hg
  let p := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨r, hr, hR⟩ := exists_domain_away_of_standardSmooth_curve (K := K) p
  let _ := hR
  let A := Localization.Away r
  let j : Spec (.of A) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) ≫ hV.fromSpec
  have hj : x ∈ Set.range j := by
    have hp : hV.primeIdealOf ⟨x, hx⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(X, V) A)) := by
      rw [PrimeSpectrum.localization_away_comap_range A r]
      exact hr
    obtain ⟨z, hz⟩ := hp
    refine ⟨z, ?_⟩
    change hV.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, V) A) z) = x
    rw [hz, hV.fromSpec_primeIdealOf]
  refine ⟨j.opensRange, hj, ?_⟩
  exact j.isoOpensRange.hom.homeomorph.irreducibleSpace_iff.mp inferInstance

/-- A connected smooth relative curve over any field is irreducible. -/
theorem smoothCurve_irreducible [ConnectedSpace X] : IrreducibleSpace X :=
  irreducibleSpace_of_connected_of_irreducible_neighborhoods
    (smoothCurve_irreducible_neighborhood f)

end FLT.Mazur.FCurve
