/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticDescent

/-!
# The integral algebra of a quadratic twist

The twist of a commutative Hopf algebra by inversion has an integral candidate:
the fixed algebra of quadratic conjugation tensored with the antipode. The
results here construct that algebra and recover the original algebra after
quadratic scalar extension. A Hopf structure on the fixed algebra requires
separate descent of comultiplication.
-/

@[expose] public section

open scoped TensorProduct QuadraticAlgebra

namespace HopfAlgebra

variable (R H : Type*) [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- Inversion on an affine commutative group scheme is involutive. -/
theorem antipode_involutive : Function.Involutive (antipode R (A := H)) := by
  have h := inv_inv (WithConv.toConv (AlgHom.id R H))
  have he : (antipodeAlgHom R H).comp (antipodeAlgHom R H) = AlgHom.id R H :=
    congrArg WithConv.ofConv h
  intro x
  exact AlgHom.congr_fun he x

/-- The antipode of a commutative Hopf algebra is an algebra involution. -/
noncomputable def antipodeAlgEquiv : H ≃ₐ[R] H :=
  AlgEquiv.ofAlgHom (antipodeAlgHom R H) (antipodeAlgHom R H)
    (AlgHom.ext (antipode_involutive R H)) (AlgHom.ext (antipode_involutive R H))

end HopfAlgebra

namespace QuadraticTwist

universe v
variable {R H : Type v} [CommRing R] [CommRing H] [Algebra R H]
variable (d : R)

/-- Conjugation in the quadratic coefficient algebra, as an algebra equivalence. -/
def conjugation : QuadraticAlgebra R d 0 ≃ₐ[R] QuadraticAlgebra R d 0 where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_mul' x y := by simp
  map_add' := star_add
  commutes' x := by ext <;> simp

/-- Conjugation negates the quadratic generator. -/
@[simp] theorem conjugation_omega :
    conjugation d QuadraticAlgebra.omega = -QuadraticAlgebra.omega := by
  ext <;> simp [conjugation]

/-- When two is invertible, conjugation fixes exactly the scalar elements. -/
theorem conjugation_eq_self_iff (r : R) (hr : 2 * r = 1)
    (z : QuadraticAlgebra R d 0) : conjugation d z = z ↔ z.im = 0 := by
  constructor
  · intro hz
    have hi : -z.im = z.im := congrArg QuadraticAlgebra.im hz
    linear_combination -r * hi - z.im * hr
  · intro hz
    ext <;> simp [conjugation, hz]

/-- The fixed coefficient algebra is the original coefficient ring. -/
noncomputable def fixedScalarsEquiv (r : R) (hr : 2 * r = 1) :
    QuadraticDescent.fixed (conjugation d) ≃ₐ[R] R := by
  refine (AlgEquiv.ofBijective (Algebra.ofId R (QuadraticDescent.fixed (conjugation d)))
    ⟨?_, ?_⟩).symm
  · intro x y h
    exact congrArg (fun z : QuadraticDescent.fixed (conjugation d) ↦ z.val.re) h
  · intro z
    refine ⟨z.val.re, Subtype.ext ?_⟩
    have hz := (conjugation_eq_self_iff d r hr z.val).mp z.property
    ext <;> simp [hz]

/-- The inverse of scalar descent is the ordinary coefficient inclusion. -/
@[simp] theorem fixedScalarsEquiv_symm_apply (r : R) (hr : 2 * r = 1) (x : R) :
    ((fixedScalarsEquiv d r hr).symm x : QuadraticAlgebra R d 0) =
      algebraMap R _ x := rfl

/-- The tensor product of quadratic conjugation and an algebra involution. -/
def involution (ι : H ≃ₐ[R] H) :
    QuadraticAlgebra R d 0 ⊗[R] H ≃ₐ[R] QuadraticAlgebra R d 0 ⊗[R] H :=
  Algebra.TensorProduct.congr (conjugation d) ι

/-- The tensor action is involutive when its second factor is involutive. -/
theorem involution_involutive (ι : H ≃ₐ[R] H) (hι : Function.Involutive ι) :
    Function.Involutive (involution d ι) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
    change star (star s) ⊗ₜ[R] ι (ι x) = s ⊗ₜ[R] x
    rw [star_star, hι]

/-- The integral fixed algebra used for descent of the quadratic twist. -/
def model (ι : H ≃ₐ[R] H) : Subalgebra R (QuadraticAlgebra R d 0 ⊗[R] H) :=
  QuadraticDescent.fixed (involution d ι)

variable (u : Rˣ)

/-- The quadratic generator is a unit when its square is a unit. -/
def omegaUnit : (QuadraticAlgebra R (u : R) 0)ˣ where
  val := QuadraticAlgebra.omega
  inv := (↑u⁻¹ : R) • QuadraticAlgebra.omega
  val_inv := by
    rw [mul_smul_comm, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp [smul_smul]
  inv_val := by
    rw [smul_mul_assoc, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp [smul_smul]

/-- The anti-invariant unit in the base-changed algebra. -/
def tensorUnit : (QuadraticAlgebra R (u : R) 0 ⊗[R] H)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft :
    QuadraticAlgebra R (u : R) 0 →ₐ[R] QuadraticAlgebra R (u : R) 0 ⊗[R] H).toMonoidHom
      (omegaUnit u)

/-- The tensor involution negates the coefficient generator. -/
theorem involution_tensorUnit (ι : H ≃ₐ[R] H) :
    involution (u : R) ι (tensorUnit (H := H) u : QuadraticAlgebra R (u : R) 0 ⊗[R] H) =
      -(tensorUnit (H := H) u : QuadraticAlgebra R (u : R) 0 ⊗[R] H) := by
  change conjugation (u : R) QuadraticAlgebra.omega ⊗ₜ[R] ι 1 =
    -(QuadraticAlgebra.omega ⊗ₜ[R] (1 : H))
  rw [conjugation_omega, map_one, TensorProduct.neg_tmul]

/-- The coefficient generator in the tensor algebra squares to the twisting unit. -/
theorem tensorUnit_sq :
    (tensorUnit (H := H) u : QuadraticAlgebra R (u : R) 0 ⊗[R] H) *
        (tensorUnit (H := H) u : QuadraticAlgebra R (u : R) 0 ⊗[R] H) =
      algebraMap R _ (u : R) := by
  change (QuadraticAlgebra.omega ⊗ₜ[R] (1 : H)) *
    (QuadraticAlgebra.omega ⊗ₜ[R] 1) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp

/-- Quadratic scalar extension recovers the untwisted algebra from its fixed model. -/
noncomputable def scalarExtensionEquiv (ι : H ≃ₐ[R] H) (hι : Function.Involutive ι)
    (r : R) (hr : 2 * r = 1) :
    QuadraticAlgebra R (u : R) 0 ⊗[R] model (u : R) ι ≃ₐ[R]
      QuadraticAlgebra R (u : R) 0 ⊗[R] H :=
  QuadraticDescent.descentEquiv (involution (u : R) ι)
    (involution_involutive (u : R) ι hι) (tensorUnit u)
    (involution_tensorUnit u ι) r hr (u : R) (tensorUnit_sq u)

/-- The fixed twist model of a finite flat algebra is finite flat over a Dedekind domain. -/
theorem model_isFiniteFlat [IsDedekindDomain R] [Module.Finite R H] [Module.Flat R H]
    (ι : H ≃ₐ[R] H) : HopfAlgebra.IsFiniteFlat R (model d ι) := by
  exact QuadraticDescent.fixed_isFiniteFlat (involution d ι)

end QuadraticTwist
