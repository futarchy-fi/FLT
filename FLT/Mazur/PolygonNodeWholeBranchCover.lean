/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonNormalizationAlgebra
public import FLT.Mazur.PolygonCyclicCocone

/-!
# Both whole affine branches cover the ordinary node

Integral normalization gives a lift of every prime to one of the two polynomial rings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped Polynomial
namespace FLT.Mazur.PolygonNodeBranches
universe u
variable (K : Type u) [Field K]

/-- Every node point belongs to one of its two complete affine branches, including the origin. -/
theorem wholeBranches_cover (y : node K) :
    y ∈ Set.range (PolygonCyclicAtlas.firstBranch K) ∨
      y ∈ Set.range (PolygonCyclicAtlas.secondBranch K) := by
  obtain ⟨p, hp⟩ := PolygonNormalizationAlgebra.node_comap_surjective y
  obtain ⟨p | p, rfl⟩ := (PrimeSpectrum.primeSpectrumProd K[X] K[X]).symm.surjective p
  · rw [PrimeSpectrum.primeSpectrumProd_symm_inl] at hp
    rw [← PrimeSpectrum.comap_comp_apply] at hp
    exact Or.inl ⟨p, hp⟩
  · rw [PrimeSpectrum.primeSpectrumProd_symm_inr] at hp
    rw [← PrimeSpectrum.comap_comp_apply] at hp
    exact Or.inr ⟨p, hp⟩

end FLT.Mazur.PolygonNodeBranches
