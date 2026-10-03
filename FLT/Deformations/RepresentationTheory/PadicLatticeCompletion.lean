/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.FiniteFreeAdicComplete
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Completion of the original finite free p-adic lattice -/

@[expose] public noncomputable section
namespace GaloisRepresentation.PrimePower
variable (p : ℕ) [Fact p.Prime] (R V : Type*) [CommRing R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]

/-- Finite free p-adic coefficient lattices are complete for the actual p-power ideal. -/
theorem isAdicComplete_padicLattice : IsAdicComplete (Ideal.span {(p : R)}) V := by
  let : Module ℤ_[p] V := Module.compHom V (algebraMap ℤ_[p] R)
  let : IsScalarTower ℤ_[p] R V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module.Finite ℤ_[p] V := Module.Finite.trans R V
  let : Module.Free ℤ_[p] V := Module.Free.trans (R := ℤ_[p]) (S := R) (M := V)
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) V :=
    (Module.finBasis ℤ_[p] V).isAdicComplete _
  have he : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] R) =
      Ideal.span {(p : R)} := by
    simp only [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← he, IsAdicComplete.map_algebraMap_iff]
  exact hc

/-- The original lattice, rather than a new model of it, maps isomorphically to its completion. -/
def padicLatticeCompletion : V ≃ₗ[R] AdicCompletion (Ideal.span {(p : R)}) V := by
  let := isAdicComplete_padicLattice p R V
  exact AdicCompletion.ofLinearEquiv _ _

/-- This comparison sends a vector to its actual residue classes. -/
theorem padicLatticeCompletion_apply (x : V) :
    padicLatticeCompletion p R V x = AdicCompletion.of (Ideal.span {(p : R)}) V x := rfl

end GaloisRepresentation.PrimePower
