/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.CotangentGenerators
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Minimal algebra generators of finite local augmented algebras

Generators of the augmentation ideal of a finite local algebra generate the
algebra. Applying the cotangent-space construction gives a polynomial
surjection with the number of variables equal to the residual cotangent
dimension. This does not bound the number of defining relations.
-/

@[expose] public noncomputable section

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A]
  [IsLocalRing A] [Algebra R A] [Module.Finite R A]

/-- In a finite local augmented algebra, ideal generators of the augmentation
ideal also generate the algebra over the base. -/
theorem adjoin_eq_top_of_span_augmentation (ε : A →ₐ[R] R) {ι : Type*}
    (x : ι → RingHom.ker ε)
    (hx : Ideal.span (Set.range (fun i ↦ (x i : A))) = RingHom.ker ε) :
    Algebra.adjoin R (Set.range (fun i ↦ (x i : A))) = ⊤ := by
  let : Nontrivial R := (algebraMap R A).domain_nontrivial
  let C := Algebra.adjoin R (Set.range (fun i ↦ (x i : A)))
  let : Module.Finite C A := Module.Finite.of_restrictScalars_finite R C A
  let : IsLocalRing C := RingHom.domain_isLocalRing (algebraMap C A)
  let J := RingHom.ker (ε.comp C.val)
  have hJ : J ≤ Ideal.jacobson (⊥ : Ideal C) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  have hmap : J.map (algebraMap C A) = RingHom.ker ε := by
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      intro c hc
      exact hc
    · rw [← hx]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      let c : C := ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
      exact Ideal.mem_map_of_mem (algebraMap C A) (show c ∈ J from (x i).property)
  let f := Algebra.linearMap C A
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    apply top_unique
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ
    intro a _
    apply Submodule.mem_sup.mpr
    refine ⟨algebraMap R A (ε a), ?_, a - algebraMap R A (ε a), ?_, ?_⟩
    · exact ⟨algebraMap R C (ε a), IsScalarTower.algebraMap_apply R C A _⟩
    · rw [Ideal.smul_top_eq_map, hmap]
      change ε (a - algebraMap R A (ε a)) = 0
      rw [map_sub, ε.commutes]
      exact sub_self _
    · exact add_sub_cancel _ _
  apply top_unique
  intro a _
  obtain ⟨c, hc⟩ := hf a
  exact hc ▸ c.property

open scoped TensorProduct

variable [IsLocalRing R] [IsNoetherianRing R]

/-- A finite local augmented algebra has a polynomial surjection in exactly
the residual cotangent dimension many variables, all with zero augmentation. -/
theorem exists_minimal_augmentation_generators (ε : A →ₐ[R] R) :
    ∃ P : Algebra.Generators R A
        (Fin (Module.finrank (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] (RingHom.ker ε).Cotangent))),
      (∀ i, ε (P.val i) = 0) ∧
      ∃ b : Module.Basis _ (IsLocalRing.ResidueField R)
          ((IsLocalRing.ResidueField R) ⊗[R] (RingHom.ker ε).Cotangent),
        ∀ i, ∃ h : P.val i ∈ RingHom.ker ε,
          1 ⊗ₜ[R] (RingHom.ker ε).toCotangent ⟨P.val i, h⟩ = b i := by
  obtain ⟨x, hx, b, hb⟩ := ε.exists_augmentation_generators
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := R) (fun i ↦ (x i : A))) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact ε.adjoin_eq_top_of_span_augmentation x hx
  refine ⟨Algebra.Generators.ofSurjective (fun i ↦ (x i : A)) hsurj,
    fun i ↦ (x i).property, b, fun i ↦ ⟨(x i).property, ?_⟩⟩
  exact hb i

end AlgHom
