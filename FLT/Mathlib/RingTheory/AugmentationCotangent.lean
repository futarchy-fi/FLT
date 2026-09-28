/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.AugmentationGenerators
public import Mathlib.Tactic.Ring

/-!
# Tangent vectors of augmented algebras

Projection onto the augmentation ideal followed by its cotangent quotient
satisfies the Leibniz rule at the augmentation. Thus every cotangent functional
is a tangent vector. Over a field, we also lift an actual basis of the cotangent
space to a minimal set of algebra generators.
-/

@[expose] public noncomputable section

namespace AlgHom

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (ε : A →ₐ[k] k)

/-- Projection onto the augmentation ideal along the scalar inclusion. -/
def augmentationProjection : A →ₗ[k] RingHom.ker ε :=
  (LinearMap.id - (Algebra.linearMap k A).comp ε.toLinearMap).codRestrict
    ((RingHom.ker ε).restrictScalars k) (fun a ↦ by simp [RingHom.mem_ker])

/-- The projection subtracts the augmented scalar. -/
@[simp] theorem augmentationProjection_coe (a : A) :
    (ε.augmentationProjection a : A) = a - algebraMap k A (ε a) := rfl

/-- Projection to the cotangent space at an augmentation. -/
def augmentationCotangent : A →ₗ[k] (RingHom.ker ε).Cotangent :=
  ((RingHom.ker ε).toCotangent.restrictScalars k).comp ε.augmentationProjection

/-- On the augmentation ideal, projection to the cotangent space is the quotient map. -/
theorem augmentationCotangent_of_mem (a : RingHom.ker ε) :
    ε.augmentationCotangent a = (RingHom.ker ε).toCotangent a := by
  have h : ε.augmentationProjection a = a := by
    apply Subtype.ext
    simp only [augmentationProjection_coe, show ε a = 0 from a.property, map_zero, sub_zero]
  exact congrArg (RingHom.ker ε).toCotangent h

/-- The cotangent projection kills the unit. -/
@[simp] theorem augmentationCotangent_one : ε.augmentationCotangent 1 = 0 := by
  have h : ε.augmentationProjection 1 = 0 := by
    apply Subtype.ext
    simp
  change (RingHom.ker ε).toCotangent (ε.augmentationProjection 1) = 0
  rw [h, map_zero]

/-- The cotangent projection satisfies Leibniz at the augmentation. -/
theorem augmentationCotangent_mul (a b : A) :
    ε.augmentationCotangent (a * b) =
      ε a • ε.augmentationCotangent b + ε b • ε.augmentationCotangent a := by
  change (RingHom.ker ε).toCotangent (ε.augmentationProjection (a * b)) =
    ε a • (RingHom.ker ε).toCotangent (ε.augmentationProjection b) +
    ε b • (RingHom.ker ε).toCotangent (ε.augmentationProjection a)
  rw [← (RingHom.ker ε).toCotangent.map_smul_of_tower (ε a) (ε.augmentationProjection b),
    ← (RingHom.ker ε).toCotangent.map_smul_of_tower (ε b) (ε.augmentationProjection a),
    ← map_add]
  apply (Ideal.toCotangent_eq _).mpr
  have h : (ε.augmentationProjection (a * b) -
      (ε a • ε.augmentationProjection b + ε b • ε.augmentationProjection a) : A) =
      (ε.augmentationProjection a : A) * (ε.augmentationProjection b : A) := by
    simp only [augmentationProjection_coe,
      map_mul, Algebra.smul_def]
    ring
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower]
  rw [h, pow_two]
  exact Ideal.mul_mem_mul (ε.augmentationProjection a).property
    (ε.augmentationProjection b).property

end AlgHom

namespace AlgHom

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  [Module.Finite k A] [IsLocalRing A]

/-- A basis of the augmentation cotangent space over the coefficient field
lifts to a minimal polynomial generating family. -/
theorem exists_augmentation_generators_of_basis (ε : A →ₐ[k] k) {ι : Type*}
    (b : Module.Basis ι k (RingHom.ker ε).Cotangent) :
    ∃ P : Algebra.Generators k A ι,
      ∀ i, ∃ h : P.val i ∈ RingHom.ker ε,
        (RingHom.ker ε).toCotangent ⟨P.val i, h⟩ = b i := by
  let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  choose x hx using fun i ↦ (RingHom.ker ε).toCotangent_surjective (b i)
  have hspan : Ideal.span (Set.range (fun i ↦ (x i : A))) = RingHom.ker ε := by
    apply Ideal.span_eq_of_span_toCotangent_eq_top _ (IsNoetherian.noetherian _)
    · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ε)
    · apply Submodule.span_eq_top_of_span_eq_top k A
      simpa only [hx] using b.span_eq
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := k) (fun i ↦ (x i : A))) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact ε.adjoin_eq_top_of_span_augmentation x hspan
  exact ⟨Algebra.Generators.ofSurjective (fun i ↦ (x i : A)) hsurj,
    fun i ↦ ⟨(x i).property, hx i⟩⟩

end AlgHom
