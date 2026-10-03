/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.PowerBasisDifferentials
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.Henselian

/-!
# Residue uniqueness for finite unramified maps

A generator has unit minimal-polynomial derivative. Two maps to a local ring
with the same residue therefore agree, without any nilpotence assumption.
-/

@[expose] public noncomputable section

namespace RaynaudParameters
open Polynomial IsLocalRing

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
  [Module.Finite R S] [Module.Free R S] [FaithfulSMul R S]
  [Algebra.FormallyUnramified R S]

/-- Residue agreement determines a map from a finite free unramified local algebra. -/
theorem unramified_hom_ext (f g : S →ₐ[R] T)
    (h : ∀ x, residue T (f x) = residue T (g x)) : f = g := by
  obtain ⟨x, hx⟩ := exists_adjoin_eq_top (R := R) (S := S)
  let pb := (IsAdjoinRootMonic.mkOfAdjoinEqTop' hx).powerBasis
  have hunit : IsUnit (aeval pb.gen (minpoly R pb.gen).derivative) := by
    rw [← Ideal.span_singleton_eq_top, Ideal.eq_top_iff_one]
    apply (pb.smul_kaehlerDifferential_eq_zero_iff 1).mp
    intro ω
    exact Subsingleton.elim _ _
  apply pb.algHom_ext
  apply eq_of_eval_eq_zero_of_not_isUnit_sub
    (f := (minpoly R pb.gen).map (algebraMap R T))
  · simp only [eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  · simp only [eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact h _
  · simpa only [derivative_map, eval_map_algebraMap, ← aeval_algHom_apply] using
      hunit.map f

end RaynaudParameters
