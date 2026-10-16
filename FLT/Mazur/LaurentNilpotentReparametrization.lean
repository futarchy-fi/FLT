/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentAlgebraAutomorphism
public import FLT.Mazur.LaurentUnitPoints
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Laurent reparametrizations with nilpotent coefficient corrections

A unit congruent to the inverse Laurent coordinate induces an automorphism
of the entire Laurent algebra, at arbitrary nilpotent order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentNilpotentReparametrization
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The positive Laurent coordinate alone determines an algebra map. -/
theorem hom_ext_positive {f g : R[T;T⁻¹] →ₐ[R] A}
    (h : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  have hu : LaurentUnitPoints.pointUnit f = LaurentUnitPoints.pointUnit g := Units.ext h
  rw [← LaurentUnitPoints.evalUnit_pointUnit f, ← LaurentUnitPoints.evalUnit_pointUnit g, hu]

/-- Congruence on the positive coordinate controls every Laurent function. -/
theorem hom_sub_mem (J : Ideal A) (f g : R[T;T⁻¹] →ₐ[R] A)
    (h : f (LaurentPolynomial.T 1) - g (LaurentPolynomial.T 1) ∈ J)
    (x : R[T;T⁻¹]) : f x - g x ∈ J := by
  have he : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g := by
    apply hom_ext_positive
    exact Ideal.Quotient.eq.mpr h
  exact Ideal.Quotient.eq.mp (congrArg (fun k : R[T;T⁻¹] →ₐ[R] A ⧸ J ↦ k x) he)

variable (I : Ideal R) (hI : IsNilpotent I) (u : R[T;T⁻¹]ˣ)
  (hu : (u : R[T;T⁻¹]) - LaurentPolynomial.T (-1) ∈ I.map (algebraMap R R[T;T⁻¹]))
local notation "L" => R[T;T⁻¹]

include hu hI in
/-- A full inverse-coordinate perturbation by a nilpotent coefficient ideal is bijective. -/
theorem evalUnit_bijective : Function.Bijective (LaurentUnitPoints.evalUnit (R := R) u) := by
  let f := LaurentUnitPoints.evalUnit (R := R) u
  have h : ∀ x : L, f x - LaurentPolynomial.invert x ∈
      I.map (algebraMap R L) := by
    refine hom_sub_mem _ f LaurentPolynomial.invert.toAlgHom ?_
    simpa only [f, LaurentUnitPoints.evalUnit_T, zpow_one,
      AlgEquiv.coe_toAlgHom, LaurentPolynomial.invert_T] using hu
  have hi : ∀ x : L, (f.comp LaurentPolynomial.invert.toAlgHom) x - x ∈
      I.map (algebraMap R L) := by
    intro x
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      LaurentPolynomial.involutive_invert x] using h (LaurentPolynomial.invert x)
  have hb := NilpotentAlgebraAutomorphism.bijective I
    (f.comp LaurentPolynomial.invert.toAlgHom) hi hI
  exact ⟨fun x y hxy ↦ by
      apply LaurentPolynomial.invert.injective
      apply hb.1
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        LaurentPolynomial.involutive_invert x,
        LaurentPolynomial.involutive_invert y] using hxy,
    fun y ↦ by
      obtain ⟨x, hx⟩ := hb.2 y
      exact ⟨LaurentPolynomial.invert x, hx⟩⟩

/-- The complete Laurent coordinate change, with its constructed inverse. -/
def equiv : L ≃ₐ[R] L :=
  AlgEquiv.ofBijective (LaurentUnitPoints.evalUnit u) (evalUnit_bijective I hI u hu)

/-- The coordinate change evaluates at the exact original unit. -/
theorem equiv_toAlgHom : (equiv I hI u hu).toAlgHom = LaurentUnitPoints.evalUnit u := rfl

end FLT.Mazur.LaurentNilpotentReparametrization
