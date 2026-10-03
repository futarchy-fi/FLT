/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Reduction of local algebra automorphisms

Reduction is a group homomorphism whose kernel is the existing ideal inertia
subgroup. No unramifiedness or lifting of automorphisms is assumed here.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- Reduction of automorphisms of a local algebra to its residue extension. -/
def residueAction : (S ≃ₐ[R] S) →* (ResidueField S ≃ₐ[ResidueField R] ResidueField S) where
  toFun := ResidueField.mapAlgEquiv'
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := residue_surjective x
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨x, rfl⟩ := residue_surjective x
    rfl

/-- Reduction agrees with the original automorphism on every residue class. -/
@[simp] theorem residueAction_apply_residue (σ : S ≃ₐ[R] S) (x : S) :
    residueAction R S σ (residue S x) = residue S (σ x) := rfl

/-- An integral automorphism acts trivially on the residue field exactly when
its displacement of every element belongs to the maximal ideal. -/
theorem residueAction_eq_one_iff (σ : S ≃ₐ[R] S) :
    residueAction R S σ = 1 ↔ ∀ x : S, σ x - x ∈ maximalIdeal S := by
  constructor
  · intro h x
    rw [← residue_eq_zero_iff, map_sub, ← residueAction_apply_residue, h]
    exact sub_self _
  · intro h
    ext x
    obtain ⟨x, rfl⟩ := residue_surjective x
    change residue S (σ x) = residue S x
    exact sub_eq_zero.mp (by simpa only [map_sub] using
      (residue_eq_zero_iff (σ x - x)).mpr (h x))

/-- The kernel is Mathlib's ideal inertia, for the natural algebra action. -/
theorem residueAction_ker :
    (residueAction R S).ker = (maximalIdeal S).inertia (S ≃ₐ[R] S) := by
  ext σ
  exact residueAction_eq_one_iff R S σ

end LocalClassFieldTheory
