/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResidualPresentationKernelMap

/-!
# Generators of a scalar-extended residual kernel

Residual flatness makes the extended old kernel span all new relations.
If the final coefficients are a quotient of another ring, linear maps over
that ring vanish once they vanish on the original kernel generators.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ResidualKernelSpan
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M]
  (A B : Type*) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The canonical comparison with its codomain restricted to the actual kernel. -/
def comparison (f : P →ₗ[R] N) :
    B ⊗[A] (f.baseChange A).ker →ₗ[B] (f.baseChange B).ker :=
  (ResidualPresentationKernelMap.comparison A B f).codRestrict _
    (ResidualPresentationKernelMap.comparison_mem_kernel A B f)

/-- Flat residual cokernel makes the constructed kernel comparison surjective. -/
theorem comparison_surjective (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)] : Function.Surjective (comparison A B f) := by
  intro z
  obtain ⟨y, hy⟩ := ResidualPresentationKernel.exists_kernel_lift A B f q he hq
    z.val z.property
  exact ⟨y, Subtype.ext hy⟩

variable (S : Type*) [CommRing S] [Algebra S B]
  {T : Type*} [AddCommGroup T] [Module S T]

/-- Lift quotient coefficients to show that killing the old generators kills every relation. -/
theorem map_eq_zero (hB : Function.Surjective (algebraMap S B))
    (f : P →ₗ[R] N) (q : N →ₗ[R] M)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)] (g : (f.baseChange B).ker →ₗ[S] T)
    (hg : ∀ x : (f.baseChange A).ker, g (comparison A B f (1 ⊗ₜ[A] x)) = 0) :
    g = 0 := by
  ext z
  obtain ⟨y, rfl⟩ := comparison_surjective A B f q he hq z
  change g (comparison A B f y) = 0
  induction y with
  | tmul b x =>
    obtain ⟨s, rfl⟩ := hB b
    have hs : algebraMap S B s ⊗ₜ[A] x = s • (1 ⊗ₜ[A] x) := by
      rw [smul_tmul', Algebra.smul_def, mul_one]
    rw [hs, LinearMap.map_smul_of_tower, map_smul, hg, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

end FLT.Mazur.ResidualKernelSpan
