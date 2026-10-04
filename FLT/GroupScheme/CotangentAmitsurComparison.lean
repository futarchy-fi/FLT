/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RelativeFlatCotangent
public import FLT.GroupScheme.AmitsurDegreeOneMaps

/-! # Cotangent functionals and the actual tensor Amitsur differentials -/

@[expose] public noncomputable section
open TensorProduct Algebra.Amitsur
namespace AlgHom
variable {R A B S M : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
  [Algebra R A] [Algebra R B] [Algebra R S] [Algebra B S] [IsScalarTower R B S]
  [Module.Free R A] [Module.Finite R A]
  [Module.Flat B S] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] (ε : A →ₐ[R] R)

/-- The canonical comparison on double cover tensors. -/
def cotangentDoubleTensorEquiv :
    S ⊗[B] (S ⊗[B] ((RingHom.ker ε).Cotangent →ₗ[R] M)) ≃ₗ[B]
      ((RingHom.ker ε).Cotangent →ₗ[R] S ⊗[B] (S ⊗[B] M)) :=
  (TensorProduct.congr (LinearEquiv.refl B S) ε.relativeFlatCotangentHomEquiv).trans
    ε.relativeFlatCotangentHomEquiv

/-- The canonical comparison on triple cover tensors. -/
def cotangentTripleTensorEquiv :
    S ⊗[B] (S ⊗[B] (S ⊗[B] ((RingHom.ker ε).Cotangent →ₗ[R] M))) ≃ₗ[B]
      ((RingHom.ker ε).Cotangent →ₗ[R] S ⊗[B] (S ⊗[B] (S ⊗[B] M))) :=
  (TensorProduct.congr (LinearEquiv.refl B S) ε.cotangentDoubleTensorEquiv).trans
    ε.relativeFlatCotangentHomEquiv

/-- Double comparison preserves the original cotangent evaluation. -/
theorem cotangentDoubleTensorEquiv_tmul (s t : S)
    (f : (RingHom.ker ε).Cotangent →ₗ[R] M) (a : (RingHom.ker ε).Cotangent) :
    ε.cotangentDoubleTensorEquiv (s ⊗ₜ[B] (t ⊗ₜ[B] f)) a = s ⊗ₜ[B] (t ⊗ₜ[B] f a) := by
  simp [cotangentDoubleTensorEquiv, relativeFlatCotangentHomEquiv_tmul]

/-- Triple comparison preserves the same evaluation. -/
theorem cotangentTripleTensorEquiv_tmul (s t u : S)
    (f : (RingHom.ker ε).Cotangent →ₗ[R] M) (a : (RingHom.ker ε).Cotangent) :
    ε.cotangentTripleTensorEquiv (s ⊗ₜ[B] (t ⊗ₜ[B] (u ⊗ₜ[B] f))) a =
      s ⊗ₜ[B] (t ⊗ₜ[B] (u ⊗ₜ[B] f a)) := by
  simp [cotangentTripleTensorEquiv, relativeFlatCotangentHomEquiv_tmul,
    cotangentDoubleTensorEquiv_tmul]

/-- The original cotangent pairing intertwines degree-zero coboundaries. -/
theorem cotangentDoubleTensorEquiv_d₀
    (z : S ⊗[B] ((RingHom.ker ε).Cotangent →ₗ[R] M))
    (a : (RingHom.ker ε).Cotangent) :
    ε.cotangentDoubleTensorEquiv (d₀ B S _ z) a =
      d₀ B S M (ε.relativeFlatCotangentHomEquiv z a) := by
  induction z using TensorProduct.inductionOn with
  | tmul s f =>
    simp only [d₀_tmul, map_sub, LinearMap.sub_apply, cotangentDoubleTensorEquiv_tmul,
      relativeFlatCotangentHomEquiv_tmul]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The original cotangent pairing intertwines degree-one cocycles. -/
theorem cotangentTripleTensorEquiv_d₁
    (z : S ⊗[B] (S ⊗[B] ((RingHom.ker ε).Cotangent →ₗ[R] M)))
    (a : (RingHom.ker ε).Cotangent) :
    ε.cotangentTripleTensorEquiv (d₁ B S _ z) a =
      d₁ B S M (ε.cotangentDoubleTensorEquiv z a) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    induction z using TensorProduct.inductionOn with
    | tmul t f =>
      simp only [d₁_tmul, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
        cotangentTripleTensorEquiv_tmul, cotangentDoubleTensorEquiv_tmul]
    | add x y hx hy => simp only [tmul_add, map_add, LinearMap.add_apply, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end AlgHom
