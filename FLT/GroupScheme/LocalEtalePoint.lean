/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Pointed finite étale extensions of local algebras

A finite étale map of local algebras is an isomorphism if the target admits a
point over the common base. The point identifies the residue fields, and
Nakayama gives surjectivity; faithful flatness gives injectivity.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A finite homomorphism between local rings is local. -/
theorem finite_algebra_isLocalHom {Q B : Type*} [CommRing Q] [CommRing B]
    [Algebra Q B] [IsLocalRing Q] [IsLocalRing B] [Module.Finite Q B] :
    IsLocalHom (algebraMap Q B) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap Q B)).out 5 1).mp
  apply IsLocalRing.eq_maximalIdeal
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    (algebraMap_isIntegral_iff.mpr inferInstance) _

/-- A finite unramified map of local algebras is surjective if the target has a
point over the common base. -/
theorem algebraMap_surjective_of_local_unramified_point
    {R Q B : Type*} [CommRing R] [Nontrivial R] [CommRing Q] [CommRing B]
    [Algebra R Q] [Algebra R B] [Algebra Q B] [IsScalarTower R Q B]
    [IsLocalRing Q] [IsLocalRing B] [Module.Finite Q B]
    [Algebra.FormallyUnramified Q B] (ε : B →ₐ[R] R) :
    Function.Surjective (algebraMap Q B) := by
  let := finite_algebra_isLocalHom (Q := Q) (B := B)
  have hε : Function.Surjective ε := fun r ↦ ⟨algebraMap R B r, ε.commutes r⟩
  let : IsLocalRing R := IsLocalRing.of_surjective' ε.toRingHom hε
  let := IsLocalHom.of_surjective ε.toRingHom hε
  let f := Algebra.linearMap Q B
  have hr : LinearMap.range f = ⊤ := by
    apply top_unique
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro b _
    rw [Ideal.smul_top_eq_map]
    apply Submodule.mem_sup.mpr
    refine ⟨algebraMap R B (ε b), ?_, b - algebraMap R B (ε b), ?_, by abel⟩
    · exact ⟨algebraMap R Q (ε b), (IsScalarTower.algebraMap_apply R Q B (ε b)).symm⟩
    · rw [Submodule.restrictScalars_mem, Algebra.FormallyUnramified.map_maximalIdeal,
        ← IsLocalRing.maximalIdeal_comap ε.toRingHom]
      change ε (b - algebraMap R B (ε b)) ∈ IsLocalRing.maximalIdeal R
      simp
  exact LinearMap.range_eq_top.mp hr

/-- A finite étale map of pointed local algebras is an isomorphism on coordinates. -/
theorem algebraMap_bijective_of_local_etale_point
    {R Q B : Type*} [CommRing R] [Nontrivial R] [CommRing Q] [CommRing B]
    [Algebra R Q] [Algebra R B] [Algebra Q B] [IsScalarTower R Q B]
    [IsLocalRing Q] [IsLocalRing B] [Module.Finite Q B]
    [Algebra.Etale Q B] (ε : B →ₐ[R] R) : Function.Bijective (algebraMap Q B) := by
  let := finite_algebra_isLocalHom (Q := Q) (B := B)
  let := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Q) (B := B)
  exact ⟨FaithfulSMul.algebraMap_injective Q B,
    algebraMap_surjective_of_local_unramified_point ε⟩

end ThreeAdicPlan
