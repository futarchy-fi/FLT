/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
public import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Quadratic descent of a fixed algebra

When two is invertible and an involution negates a unit whose square lies in
the coefficient ring, its fixed algebra recovers the original algebra after
quadratic scalar extension. This is algebra descent; descent of a Hopf
structure requires compatibility with comultiplication and counit as well.
-/

@[expose] public section

open scoped TensorProduct QuadraticAlgebra

namespace QuadraticDescent

universe v
variable {R B : Type v} [CommRing R] [CommRing B] [Algebra R B]
variable (σ : B ≃ₐ[R] B) (hσ : Function.Involutive σ) (t : Bˣ)
  (ht : σ (t : B) = -(t : B)) (r : R) (hr : 2 * r = 1)

/-- The fixed algebra of the semilinear involution. -/
def fixed : Subalgebra R B := AlgHom.equalizer σ.toAlgHom (AlgHom.id R B)

include ht in
/-- The involution negates the inverse of its anti-invariant unit. -/
theorem map_inv_unit : σ (↑t⁻¹ : B) = -(↑t⁻¹ : B) := by
  have h : Units.map σ.toAlgHom.toRingHom.toMonoidHom t = -t := Units.ext ht
  have hi : Units.map σ.toAlgHom.toRingHom.toMonoidHom t⁻¹ = -t⁻¹ := by
    rw [map_inv, h]
    simp
  exact congrArg Units.val hi

/-- Projection onto the invariant summand. -/
noncomputable def evenPart (x : B) : fixed σ :=
  ⟨algebraMap R B r * (x + σ x), by
    change σ (algebraMap R B r * (x + σ x)) = _
    simp [hσ x, add_comm]⟩

/-- The anti-invariant summand divided by the anti-invariant unit. -/
noncomputable def oddPart (x : B) : fixed σ :=
  ⟨(↑t⁻¹ : B) * algebraMap R B r * (x - σ x), by
    change σ ((↑t⁻¹ : B) * algebraMap R B r * (x - σ x)) = _
    rw [map_mul, map_mul, map_sub, σ.commutes, hσ x, map_inv_unit σ t ht]
    simp only [AlgHom.id_apply]
    ring⟩

include hr in
/-- Every element splits into an invariant part and the unit times an invariant part. -/
theorem decomposition (x : B) :
    (evenPart σ hσ r x : B) + (t : B) * oddPart σ hσ t ht r x = x := by
  have h : (2 : B) * algebraMap R B r = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg (algebraMap R B) hr
  change algebraMap R B r * (x + σ x) +
    (t : B) * ((↑t⁻¹ : B) * algebraMap R B r * (x - σ x)) = x
  rw [← mul_assoc (t : B), ← mul_assoc (t : B), Units.mul_inv, one_mul]
  linear_combination x * h

include ht hr in
/-- Invariant and anti-invariant coefficients determine an element uniquely. -/
theorem coefficients_unique (a b : fixed σ) (h : (a : B) + (t : B) * b = 0) :
    a = 0 ∧ b = 0 := by
  have ha : σ (a : B) = a := a.property
  have hb : σ (b : B) = b := b.property
  have hs := congrArg σ h
  simp only [map_add, map_mul, ha, hb, ht, map_zero] at hs
  have h2 : (2 : B) * algebraMap R B r = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg (algebraMap R B) hr
  have ha0 : (a : B) = 0 := by
    linear_combination algebraMap R B r * h + algebraMap R B r * hs - (a : B) * h2
  have hb0 : (b : B) = 0 := by
    rw [ha0, zero_add] at h
    exact t.isUnit.mul_left_cancel (by simpa using h)
  exact ⟨Subtype.ext ha0, Subtype.ext hb0⟩

variable (d : R) (htsq : (t : B) * t = algebraMap R B d)

/-- The quadratic coefficient algebra maps to the algebra carrying the involution. -/
noncomputable def coefficientMap : QuadraticAlgebra R d 0 →ₐ[R] B :=
  QuadraticAlgebra.lift ⟨(t : B), by simpa [Algebra.smul_def] using htsq⟩

/-- Multiplication gives the canonical scalar-extension map from the fixed algebra. -/
noncomputable def descentMap : QuadraticAlgebra R d 0 ⊗[R] fixed σ →ₐ[R] B :=
  Algebra.TensorProduct.lift (coefficientMap t d htsq) (fixed σ).val (fun _ _ ↦ .all _ _)

/-- Every tensor over a quadratic algebra has two coefficients. -/
theorem tensor_decomposition (z : QuadraticAlgebra R d 0 ⊗[R] fixed σ) :
    ∃ a b : fixed σ, z = 1 ⊗ₜ[R] a + QuadraticAlgebra.omega ⊗ₜ[R] b := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨c, e, rfl⟩ := hw
    refine ⟨a + c, b + e, ?_⟩
    simp only [TensorProduct.tmul_add]
    abel
  | tmul z a =>
    refine ⟨z.re • a, z.im • a, ?_⟩
    conv_lhs => rw [← QuadraticAlgebra.re_smul_add_im_smul z]
    simp only [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]

include hσ ht hr in
/-- The fixed algebra recovers the original algebra after quadratic scalar extension. -/
theorem descentMap_bijective : Function.Bijective (descentMap σ t d htsq) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨a, b, rfl⟩ := tensor_decomposition σ d z
    have hz' : (a : B) + (t : B) * b = 0 := by
      simpa [descentMap, coefficientMap, QuadraticAlgebra.lift] using hz
    obtain ⟨rfl, rfl⟩ := coefficients_unique σ t ht r hr a b hz'
    simp
  · intro x
    refine ⟨1 ⊗ₜ[R] evenPart σ hσ r x +
      QuadraticAlgebra.omega ⊗ₜ[R] oddPart σ hσ t ht r x, ?_⟩
    simpa [descentMap, coefficientMap, QuadraticAlgebra.lift] using
      decomposition σ hσ t ht r hr x

/-- Scalar extension identifies the fixed algebra with the algebra carrying the involution. -/
noncomputable def descentEquiv : QuadraticAlgebra R d 0 ⊗[R] fixed σ ≃ₐ[R] B :=
  AlgEquiv.ofBijective (descentMap σ t d htsq) (descentMap_bijective σ hσ t ht r hr d htsq)

/-- Over a Dedekind domain, the fixed algebra of a finite torsion-free algebra is finite flat.
This statement concerns the underlying module and does not supply a Hopf structure. -/
theorem fixed_isFiniteFlat [IsDedekindDomain R] [Module.Finite R B]
    [Module.IsTorsionFree R B] : HopfAlgebra.IsFiniteFlat R (fixed σ) := by
  let : Module.Finite R (fixed σ) := Module.Finite.of_injective (fixed σ).val.toLinearMap
    Subtype.val_injective
  let : Module.IsTorsionFree R (fixed σ) :=
    Function.Injective.moduleIsTorsionFree (fixed σ).val Subtype.val_injective
      (fun a b ↦ (fixed σ).val.toLinearMap.map_smul a b)
  exact ⟨⟩

end QuadraticDescent
