/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatAugmentationTangent

/-! # Flat cotangent comparison preserves source maps and coefficient maps -/

@[expose] public noncomputable section
open TensorProduct
namespace AlgHom
variable {R A A' M N T : Type*} [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Module.Free R A] [Module.Finite R A]
  [Module.Free R A'] [Module.Finite R A']
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup T]
  [Module R M] [Module R N] [Module R T] [Module.Flat R T]
  (ε : A →ₐ[R] R) (ε' : A' →ₐ[R] R)

/-- Flat tensor comparison commutes with the original contravariant cotangent map. -/
theorem flatCotangentHomEquiv_precomp
    (f : (RingHom.ker ε').Cotangent →ₗ[R] (RingHom.ker ε).Cotangent)
    (z : T ⊗[R] ((RingHom.ker ε).Cotangent →ₗ[R] M)) :
    ε'.flatCotangentHomEquiv (f.relationPrecomp.lTensor T z) =
      (ε.flatCotangentHomEquiv z).comp f := by
  induction z using TensorProduct.inductionOn with
  | tmul t g =>
    ext a
    change ε'.flatCotangentHomEquiv (t ⊗ₜ[R] (g.comp f)) a =
      ε.flatCotangentHomEquiv (t ⊗ₜ[R] g) (f a)
    rw [flatCotangentHomEquiv_tmul, flatCotangentHomEquiv_tmul]
    rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy, LinearMap.add_comp]

/-- Flat comparison is natural for every actual coefficient map. -/
theorem flatCotangentHomEquiv_postcomp (g : M →ₗ[R] N)
    (z : T ⊗[R] ((RingHom.ker ε).Cotangent →ₗ[R] M)) :
    ε.flatCotangentHomEquiv
      (((LinearMap.llcomp R (RingHom.ker ε).Cotangent M N) g).lTensor T z) =
      (g.lTensor T).comp (ε.flatCotangentHomEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | tmul t f =>
    ext a
    change ε.flatCotangentHomEquiv (t ⊗ₜ[R] (g.comp f)) a =
      g.lTensor T (ε.flatCotangentHomEquiv (t ⊗ₜ[R] f) a)
    rw [flatCotangentHomEquiv_tmul, flatCotangentHomEquiv_tmul]
    rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy, LinearMap.comp_add]

end AlgHom
