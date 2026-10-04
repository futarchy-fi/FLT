/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.AugmentationCotangent

/-! # Tangent functionals at an augmentation with arbitrary module values -/

@[expose] public noncomputable section
namespace AlgHom
variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] (ε : A →ₐ[R] R)

/-- Tangent functionals obey Leibniz at the actual augmentation, with arbitrary module values. -/
def augmentationTangent : Submodule R (A →ₗ[R] M) where
  carrier := {d | ∀ a b, d (a * b) = ε a • d b + ε b • d a}
  zero_mem' := by simp
  add_mem' hd he := by
    intro a b
    simp only [LinearMap.add_apply, hd a b, he a b, smul_add]
    abel
  smul_mem' r d hd := by
    intro a b
    simp only [LinearMap.smul_apply, hd a b, smul_add, smul_comm r]

variable {ε}

/-- A tangent functional kills the unit. -/
theorem augmentationTangent_one (d : ε.augmentationTangent (M := M)) : d.val 1 = 0 := by
  have h := d.property 1 1
  simp only [one_mul, map_one, one_smul] at h
  exact (add_eq_left.mp h.symm)

/-- It therefore kills every original scalar. -/
theorem augmentationTangent_algebraMap (d : ε.augmentationTangent (M := M)) (r : R) :
    d.val (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, augmentationTangent_one, smul_zero]

/-- Tangent functionals vanish on the square of the original augmentation ideal. -/
theorem augmentationTangent_square (d : ε.augmentationTangent (M := M))
    {a : A} (ha : a ∈ RingHom.ker ε ^ 2) : d.val a = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun a ha b hb ↦ ?_) (fun a b hda hdb ↦ ?_)
  · rw [d.property, show ε a = 0 from ha, show ε b = 0 from hb, zero_smul, zero_smul, add_zero]
  · rw [map_add, hda, hdb, add_zero]

/-- Restricting to the actual augmentation ideal descends through its actual square. -/
def augmentationTangentToCotangent (d : ε.augmentationTangent (M := M)) :
    (RingHom.ker ε).Cotangent →ₗ[R] M :=
  (((RingHom.ker ε) • ⊤ : Submodule A (RingHom.ker ε)).restrictScalars R).liftQ
    (d.val.comp ((RingHom.ker ε).subtype.restrictScalars R)) (by
      intro a ha
      apply augmentationTangent_square d
      apply (Ideal.toCotangent_eq_zero _ a).mp
      exact Submodule.Quotient.mk_eq_zero _ |>.mpr ha)

/-- Descent evaluates on an original ideal representative by the original functional. -/
theorem augmentationTangentToCotangent_mk (d : ε.augmentationTangent (M := M))
    (a : RingHom.ker ε) :
    augmentationTangentToCotangent d ((RingHom.ker ε).toCotangent a) = d.val a := rfl

/-- Descent composed with the actual augmentation projection recovers the functional. -/
theorem augmentationTangentToCotangent_projection (d : ε.augmentationTangent (M := M)) (a : A) :
    augmentationTangentToCotangent d (ε.augmentationCotangent a) = d.val a := by
  change d.val (a - algebraMap R A (ε a)) = d.val a
  rw [map_sub, augmentationTangent_algebraMap, sub_zero]

end AlgHom
