/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedCyclicStages

/-!
# Frobenius determines continuous discrete characters

A neighborhood of one contains a finite-stage fixing subgroup. Cyclicity
at that stage shows that an open subgroup containing Frobenius is the whole group.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing
open scoped Topology

variable (R K C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]


local notation "U" => maximalUnramified R K C
local notation "Frob" => unramifiedFrobenius R K C

/-- Every open subgroup containing arithmetic Frobenius is the whole unramified Galois group. -/
theorem unramifiedFrobenius_openSubgroup (S : Subgroup Gal(U/K))
    (hS : IsOpen (S : Set Gal(U/K))) (hF : Frob ∈ S) : S = ⊤ := by
  obtain ⟨E, hE, hES⟩ := (krullTopology_mem_nhds_one_iff K U _).mp
    (hS.mem_nhds S.one_mem)
  let := hE
  let := (IntermediateField.liftAlgEquiv E).toLinearEquiv.finiteDimensional
  obtain ⟨n, hn⟩ := exists_unramifiedStage_of_finite_le R K C
    (IntermediateField.lift E) (IntermediateField.lift_le E)
  let N : UnramifiedIndex := ⟨n⟩
  let T := unramifiedFiniteStage R K C N
  have hET : E ≤ T.toIntermediateField := by
    intro x hx
    exact (mem_unramifiedFiniteStage R K C N x).mpr
      (hn ((IntermediateField.mem_lift x).mpr hx))
  apply top_unique
  intro σ _
  obtain ⟨j, hj⟩ := unramifiedStageFrobenius_mem_zpowers R K C N (σ.restrictNormal T)
  have hrest : (AlgEquiv.restrictNormalHom T) (Frob ^ j) = σ.restrictNormal T := by
    rw [map_zpow]
    change ((Frob).restrictNormal T) ^ j = _
    rw [unramifiedFrobenius_restrict]
    exact hj
  have hker : σ * (Frob ^ j)⁻¹ ∈ T.toIntermediateField.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    change (AlgEquiv.restrictNormalHom T) (σ * (Frob ^ j)⁻¹) = 1
    rw [map_mul, map_inv, hrest]
    exact mul_inv_cancel _
  have hσ := S.mul_mem (hES (E.fixingSubgroup_le hET hker))
    (S.zpow_mem hF j)
  simpa using hσ

/-- A continuous homomorphism into a discrete group is determined by Frobenius. -/
theorem unramifiedCharacter_ext {A : Type*} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    (χ ψ : Gal(U/K) →ₜ* A) (h : χ Frob = ψ Frob) : χ = ψ := by
  let S := χ.toMonoidHom.eqLocus ψ.toMonoidHom
  have hS : IsOpen (S : Set Gal(U/K)) :=
    (isOpen_discrete {p : A × A | p.1 = p.2}).preimage (χ.continuous.prodMk ψ.continuous)
  have htop := unramifiedFrobenius_openSubgroup R K C S hS h
  ext σ
  have hσ : σ ∈ S := by rw [htop]; trivial
  exact hσ

/-- Evaluation at arithmetic Frobenius is injective on continuous discrete characters. -/
theorem unramifiedFrobeniusEvaluation_injective {A : Type*} [Group A]
    [TopologicalSpace A] [DiscreteTopology A] :
    Function.Injective (fun χ : Gal(U/K) →ₜ* A => χ Frob) :=
  fun χ ψ h => unramifiedCharacter_ext R K C χ ψ h

end LocalClassFieldTheory
