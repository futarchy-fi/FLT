/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.QuasiFinitePrincipalNeighbourhood

/-! # Spread a zero-dimensional residue fibre to a principal neighbourhood -/

@[expose] public noncomputable section

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [FiniteType R S]

/-- A finite-type algebra with a zero-dimensional whole fibre at the contracted prime
is quasi-finite at the specified point. This uses fibre dimension, not stalk dimension. -/
theorem quasiFiniteAt_of_fibre_dimension_zero (q : PrimeSpectrum S)
    (h : ringKrullDim ((q.asIdeal.under R).Fiber S) ≤ 0) :
    QuasiFiniteAt R q.asIdeal := by
  let p := q.comap (algebraMap R S)
  have : Ring.KrullDimLE 0 (p.asIdeal.Fiber S) := (Ring.krullDimLE_iff (n := 0)).mpr h
  have : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    (Module.finite_iff_krullDimLE_zero _ _).mpr inferInstance
  have : DiscreteTopology (PrimeSpectrum (p.asIdeal.Fiber S)) :=
    QuasiFinite.discreteTopology_primeSpectrum p.asIdeal.ResidueField _
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  apply QuasiFiniteAt.of_isOpen_singleton_fiber q
  rw [← e.isOpen_image, Set.image_singleton]
  exact isOpen_discrete _

/-- At every point of a zero-dimensional fibre there is a principal neighbourhood whose
fibres over all base primes are finite-dimensional. -/
theorem exists_principal_of_fibre_dimension_zero (q : PrimeSpectrum S)
    (h : ringKrullDim ((q.asIdeal.under R).Fiber S) ≤ 0) :
    ∃ a : S, a ∉ q.asIdeal ∧ QuasiFinite R (Localization.Away a) := by
  have := quasiFiniteAt_of_fibre_dimension_zero q h
  exact QuasiFiniteAt.exists_principal_neighbourhood q.asIdeal

end Algebra
