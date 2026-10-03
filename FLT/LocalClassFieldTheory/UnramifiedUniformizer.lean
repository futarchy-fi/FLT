/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ResidueNorm
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Uniformizers in unramified local extensions

A base uniformizer generates the actual maximal ideal upstairs. In a DVR
upstairs its image is therefore nonzero and again a uniformizer.
-/

@[expose] public section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module.Finite R S] [Algebra.FormallyUnramified R S]
  {π : R} (hπ : Irreducible π)

include hπ

/-- The same uniformizer generates the maximal ideal upstairs. -/
theorem unramified_maximalIdeal_eq :
    maximalIdeal S = Ideal.span {algebraMap R S π} := by
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S),
    hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/-- A base uniformizer stays nonzero in the unramified DVR. -/
theorem unramified_uniformizer_ne_zero : algebraMap R S π ≠ 0 := by
  intro h
  have he := unramified_maximalIdeal_eq R S hπ
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at he
  exact IsDiscreteValuationRing.not_a_field S he

/-- A base uniformizer is an upstairs uniformizer. -/
theorem unramified_uniformizer_irreducible : Irreducible (algebraMap R S π) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2
    (unramified_maximalIdeal_eq R S hπ)

end LocalClassFieldTheory
