/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RelativeFlatCotangent

/-! # Relative cotangent comparison retains source transitions and maps of flat covers -/

@[expose] public noncomputable section
open TensorProduct
namespace AlgHom
variable {R A A' B S T M : Type*} [CommRing R] [CommRing A] [CommRing A']
  [CommRing B] [CommRing S] [CommRing T] [Algebra R A] [Algebra R A'] [Algebra R B]
  [Algebra B S] [Algebra R S] [IsScalarTower R B S] [Module.Flat B S]
  [Algebra B T] [Algebra R T] [IsScalarTower R B T] [Module.Flat B T]
  [Module.Free R A] [Module.Finite R A] [Module.Free R A'] [Module.Finite R A']
  [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
  (ε : A →ₐ[R] R) (ε' : A' →ₐ[R] R)

/-- Comparison commutes with the given original cotangent map over the test algebra. -/
theorem relativeFlatCotangentHomEquiv_precomp
    (f : (RingHom.ker ε').Cotangent →ₗ[R] (RingHom.ker ε).Cotangent)
    (z : S ⊗[B] ((RingHom.ker ε).Cotangent →ₗ[R] M)) :
    ε'.relativeFlatCotangentHomEquiv (f.relativeRelationPrecomp.lTensor S z) =
      (ε.relativeFlatCotangentHomEquiv z).comp f := by
  induction z using TensorProduct.inductionOn with
  | tmul s g =>
    ext a
    change ε'.relativeFlatCotangentHomEquiv (s ⊗ₜ[B] (g.comp f)) a =
      ε.relativeFlatCotangentHomEquiv (s ⊗ₜ[B] g) (f a)
    rw [relativeFlatCotangentHomEquiv_tmul, relativeFlatCotangentHomEquiv_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]

/-- Maps between actual flat covers commute with the original cotangent comparison. -/
theorem relativeFlatCotangentHomEquiv_coverMap (α : S →ₐ[B] T)
    (z : S ⊗[B] ((RingHom.ker ε).Cotangent →ₗ[R] M)) :
    ε.relativeFlatCotangentHomEquiv (α.toLinearMap.rTensor _ z) =
      ((α.toLinearMap.rTensor M).restrictScalars R).comp
        (ε.relativeFlatCotangentHomEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s f =>
    ext a
    change ε.relativeFlatCotangentHomEquiv (α s ⊗ₜ[B] f) a =
      α.toLinearMap.rTensor M (ε.relativeFlatCotangentHomEquiv (s ⊗ₜ[B] f) a)
    rw [relativeFlatCotangentHomEquiv_tmul, relativeFlatCotangentHomEquiv_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_add]

end AlgHom
