/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# The integral algebra underlying Cartier duality

The linear dual of a cocommutative Hopf algebra carries the convolution
algebra structure. For finite projective coordinate algebras this algebra is
again finite and flat. Evaluation identifies the convolution dual of a group
algebra with the algebra of functions on its group, over the integral base.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

/-- The linear dual, equipped with convolution multiplication. -/
abbrev CartierDual (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] :=
  WithConv (Module.Dual R A)

namespace CartierDual

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]

/-- Forgetting convolution gives the ordinary linear dual. -/
def linearEquiv : CartierDual R A ≃ₗ[R] Module.Dual R A := WithConv.linearEquiv R _

/-- A finite projective module has finite convolution dual. -/
instance [Module.Finite R A] [Module.Projective R A] :
    Module.Finite R (CartierDual R A) :=
  Module.Finite.equiv (linearEquiv (R := R) (A := A)).symm

/-- A finite projective module has projective convolution dual. -/
instance [Module.Finite R A] [Module.Projective R A] :
    Module.Projective R (CartierDual R A) :=
  Module.Projective.of_equiv (linearEquiv (R := R) (A := A)).symm

/-- The integral convolution dual of a finite projective cocommutative Hopf
algebra is finite and flat. -/
instance [Module.Finite R A] [Module.Projective R A] [Coalgebra.IsCocomm R A] :
    IsFiniteFlat R (CartierDual R A) := ⟨⟩

/-- Dualizing an integral Hopf map is precomposition of linear functionals. -/
def map [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B] (f : A →ₐc[R] B) :
    CartierDual R B →ₐ[R] CartierDual R A where
  toFun φ := WithConv.toConv (φ.ofConv.comp f.toLinearMap)
  map_zero' := by rfl
  map_add' _ _ := by rfl
  map_one' := by
    apply WithConv.ext
    ext a
    simp
  map_mul' φ ψ := by
    apply WithConv.ext
    exact LinearMap.convMul_comp_coalgHom_distrib φ ψ f.toCoalgHom
  commutes' r := by
    apply WithConv.ext
    ext a
    simp

/-- Evaluation of the contravariant dual algebra map. -/
@[simp] theorem map_apply [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B]
    (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) : map f φ a = φ (f a) := rfl

/-- Evaluation on group-like basis elements identifies the dual of a group
algebra with the integral algebra of functions on the group. -/
def groupAlgebraEquiv (R G : Type*) [CommRing R] [CommGroup G] :
    CartierDual R (MonoidAlgebra R G) ≃ₐ[R] (G → R) :=
  { (WithConv.linearEquiv R _).trans ((MonoidAlgebra.basis G R).constr R).symm with
    map_mul' := by
      intro φ ψ
      funext g
      change (φ * ψ) (MonoidAlgebra.single g 1) =
        φ (MonoidAlgebra.single g 1) * ψ (MonoidAlgebra.single g 1)
      simp
    commutes' := by
      intro r
      funext g
      change algebraMap R (CartierDual R (MonoidAlgebra R G)) r
        (MonoidAlgebra.single g 1) = r
      simp }

/-- The function corresponding to a dual group-algebra element is its value
on each group-like generator. -/
@[simp] theorem groupAlgebraEquiv_apply (R G : Type*) [CommRing R] [CommGroup G]
    (φ : CartierDual R (MonoidAlgebra R G)) (g : G) :
    groupAlgebraEquiv R G φ g = φ (MonoidAlgebra.single g 1) := rfl

end CartierDual
end HopfAlgebra
