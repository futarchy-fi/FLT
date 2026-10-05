/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjBaseChangeMap
public import FLT.Mazur.HomogeneousLocalizationScalars
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Basic

/-!
# Comparison for scalar extension of homogeneous localizations

The map on degree-zero fractions extends linearly to the tensor product.
-/

@[expose] public noncomputable section
open HomogeneousLocalization
open scoped TensorProduct FLT.Mazur.HomogeneousLocalizationScalars
universe u
namespace FLT.Mazur.HomogeneousLocalizationBaseChange
open GradedProjBaseChangeMap HomogeneousLocalizationScalars
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Structural scalars on the target factor through the extended base ring. -/
local instance targetAlgebra : Algebra R (Away (baseGrade (B := B) 𝒜) (inclusion 𝒜 f)) :=
  ((algebraMap B (Away (baseGrade (B := B) 𝒜) (inclusion 𝒜 f))).comp
    (algebraMap R B)).toAlgebra

/-- The extended base and structural scalars form the expected tower. -/
local instance targetTower : IsScalarTower R B
    (Away (baseGrade (B := B) 𝒜) (inclusion 𝒜 f)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Homogeneous localization of the inclusion is an algebra map on structural scalars. -/
def awayMapAlgHom : Away 𝒜 f →ₐ[R] Away (baseGrade (B := B) 𝒜) (inclusion 𝒜 f) where
  __ := Away.map (inclusion 𝒜) f
  commutes' := awayMap_scalar 𝒜 f

/-- The natural homogeneous-localization comparison after scalar extension. -/
def comparison : B ⊗[R] Away 𝒜 f →ₐ[B]
    Away (baseGrade (B := B) 𝒜) (inclusion 𝒜 f) :=
  AlgHom.liftEquiv R B (Away 𝒜 f) _ (awayMapAlgHom (B := B) 𝒜 f)

/-- The comparison sends a scalar tensor to the scalar multiple of the localized fraction. -/
lemma comparison_tmul (b : B) (x : Away 𝒜 f) :
    comparison (B := B) 𝒜 f (b ⊗ₜ[R] x) = b • Away.map (inclusion 𝒜) f x := rfl

/-- On tensor fractions the numerator is extended and the denominator is unchanged. -/
lemma comparison_tmul_mk {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) (b : B) :
    comparison (B := B) 𝒜 f (b ⊗ₜ[R] Away.mk 𝒜 hf n a ha) =
      Away.mk (baseGrade (B := B) 𝒜) ((inclusion 𝒜).map_mem hf) n (b ⊗ₜ[R] a)
        (Submodule.tmul_mem_baseChange_of_mem b ha) := by
  rw [comparison_tmul, Away.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [val_smul, Away.val_mk, Away.val_mk]
  change b • Localization.mk (1 ⊗ₜ[R] a) ⟨(1 ⊗ₜ[R] f) ^ n, _⟩ = _
  rw [Localization.smul_mk]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

/-- Every homogeneous fraction after base change comes from a finite sum of scalar tensors. -/
lemma comparison_surjective {d : ℕ} (hf : f ∈ 𝒜 d) :
    Function.Surjective (comparison (B := B) 𝒜 f) := by
  intro x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (baseGrade (B := B) 𝒜)
    ((inclusion 𝒜).map_mem hf) x
  obtain ⟨s, rfl⟩ := ha
  induction s using TensorProduct.inductionOn with
  | tmul b a =>
    exact ⟨b ⊗ₜ[R] Away.mk 𝒜 hf n a a.property,
      comparison_tmul_mk 𝒜 f hf n a a.property b⟩
  | add s t hs ht =>
    obtain ⟨s', hs'⟩ := hs
    obtain ⟨t', ht'⟩ := ht
    refine ⟨s' + t', ?_⟩
    rw [map_add, hs', ht']
    apply HomogeneousLocalization.val_injective
    simp only [val_add, Away.val_mk, map_add, Localization.add_mk_self]

end FLT.Mazur.HomogeneousLocalizationBaseChange
