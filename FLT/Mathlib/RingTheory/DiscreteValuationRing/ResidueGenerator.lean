/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.Monogenic

/-!
# Lifting a separable residue generator

Taylor expansion allows a lift of a simple residue root to be adjusted by a
uniformizer so that its polynomial value is itself a uniformizer.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain S] [IsDiscreteValuationRing S]

/-- A simple residue root can be lifted so that its polynomial value is a
uniformizer, by adding a uniformizer to the original lift if necessary. -/
theorem exists_lift_irreducible_aeval (f : R[X]) (x : S)
    (hx : aeval x f ∈ maximalIdeal S) (hder : IsUnit (aeval x f.derivative)) :
    ∃ y : S, residue S y = residue S x ∧ Irreducible (aeval y f) := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  have hπres : residue S π = 0 := (residue_eq_zero_iff _).mpr hπ.not_isUnit
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (hπ.maximalIdeal_eq ▸ hx)
  by_cases hau : IsUnit a
  · exact ⟨x, rfl, ha ▸ irreducible_mul_iff.mpr (Or.inl ⟨hπ, hau⟩)⟩
  · have hares : residue S a = 0 := (residue_eq_zero_iff _).mpr hau
    obtain ⟨c, hc⟩ := (f.map (algebraMap R S)).exists_mul_sq_add_linear_part_eq_eval_add x π
    simp only [derivative_map, eval_map_algebraMap] at hc
    have hunit : IsUnit (c * π + aeval x f.derivative + a) := by
      rw [← residue_ne_zero_iff_isUnit]
      simpa [hπres, hares] using (residue_ne_zero_iff_isUnit _).mpr hder
    refine ⟨x + π, by simp [hπres], ?_⟩
    have heq : aeval (x + π) f = π * (c * π + aeval x f.derivative + a) := by
      rw [← hc, ha]
      ring
    rw [heq]
    exact irreducible_mul_iff.mpr (Or.inl ⟨hπ, hunit⟩)

end IsDiscreteValuationRing

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsDomain S] [IsDiscreteValuationRing S]
  [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]

/-- A finite DVR algebra with separable residue extension is monogenic. -/
theorem exists_adjoin_eq_top_of_separable_residue :
    ∃ y : S, Algebra.adjoin R {y} = ⊤ := by
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element (ResidueField R) (ResidueField S)
  obtain ⟨x, hx⟩ := residue_surjective (R := S) β
  obtain ⟨f, hf⟩ := Polynomial.map_surjective (residue R) residue_surjective
    (minpoly (ResidueField R) β)
  have heval (z : S) (g : R[X]) :
      residue S (aeval z g) = aeval (residue S z) (g.map (residue R)) :=
    map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl g z
  have hfx : aeval x f ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, heval, hf, hx]
    exact minpoly.aeval _ _
  have hfder : IsUnit (aeval x f.derivative) := by
    rw [← residue_ne_zero_iff_isUnit, heval, ← derivative_map, hf, hx]
    exact (Algebra.IsSeparable.isSeparable (ResidueField R) β).aeval_derivative_ne_zero
      (minpoly.aeval _ _)
  obtain ⟨y, hy, hfy⟩ :=
    IsDiscreteValuationRing.exists_lift_irreducible_aeval f x hfx hfder
  refine ⟨y, (Algebra.adjoin R {y}).eq_top_of_residue_surjective_of_irreducible ?_
    hfy (aeval_mem_adjoin_singleton R y)⟩
  have hgen : Algebra.adjoin (ResidueField R) {residue S y} = ⊤ := by
    rw [hy, hx,
      ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite _ _),
      hβ, IntermediateField.top_toSubalgebra]
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hgen
  intro s
  obtain ⟨p, hp⟩ := hgen (residue S s)
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (residue R) residue_surjective p
  exact ⟨⟨aeval y q, aeval_mem_adjoin_singleton R y⟩, by
    change residue S (aeval y q) = residue S s
    rw [heval, hq, hp]⟩

end IsLocalRing

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsDomain S] [IsDiscreteValuationRing S]
  [Module.Finite R S] [Module.Free R S] [IsLocalHom (algebraMap R S)]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]

/-- A finite free DVR algebra with separable residue extension has a power basis. -/
theorem nonempty_powerBasis_of_separable_residue : Nonempty (PowerBasis R S) := by
  obtain ⟨y, hy⟩ := exists_adjoin_eq_top_of_separable_residue (R := R) (S := S)
  exact ⟨(IsAdjoinRootMonic.mkOfAdjoinEqTop' hy).powerBasis⟩

end IsLocalRing
