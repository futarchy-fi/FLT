/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Integrality under integral admissible coordinate changes

An integral variable change with unit u preserves the condition that both
affine coordinates are integral. Thus it also preserves the nonintegral
chart used to characterize reduction to infinity.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- Multiplication by an integral unit reflects integrality in the fraction field. -/
theorem integral_unit_mul_mem_iff (u : Aˣ) (x : K) :
    (u : A) * x ∈ A ↔ x ∈ A := by
  constructor
  · intro h
    have hi : ((u⁻¹ : Aˣ) : A) * ((u : A) * x) ∈ A :=
      A.toSubring.mul_mem ((u⁻¹ : Aˣ) : A).property h
    have hu : (((u⁻¹ : Aˣ) : A) : K) * ((u : A) : K) = 1 := by
      exact_mod_cast u.inv_mul
    simpa only [← mul_assoc, hu, one_mul] using hi
  · exact fun h => A.toSubring.mul_mem (u : A).property h

/-- The transformed x coordinate is integral exactly when the original x coordinate is. -/
theorem variableChange_x_mem_iff (C : VariableChange A) (x : K) :
    ((C.u : A) : K) ^ 2 * x + (C.r : K) ∈ A ↔ x ∈ A := by
  have hm : ((C.u : A) : K) ^ 2 * x ∈ A ↔ x ∈ A :=
    integral_unit_mul_mem_iff A (C.u ^ 2) x
  constructor
  · intro h
    apply hm.mp
    simpa using A.sub_mem h C.r.property
  · exact fun h => A.toSubring.add_mem (hm.mpr h) C.r.property

/-- Integral unit variable changes preserve integrality of both affine coordinates. -/
theorem variableChange_coordinates_mem_iff (C : VariableChange A) (x y : K) :
    (((C.u : A) : K) ^ 2 * x + (C.r : K) ∈ A ∧
      ((C.u : A) : K) ^ 3 * y + ((C.u : A) : K) ^ 2 * (C.s : K) * x + (C.t : K) ∈ A) ↔
      x ∈ A ∧ y ∈ A := by
  have hs (hx : x ∈ A) : ((C.u : A) : K) ^ 2 * (C.s : K) * x ∈ A :=
    A.toSubring.mul_mem (A.toSubring.mul_mem (A.pow_mem (C.u : A).property 2) C.s.property) hx
  have hm : ((C.u : A) : K) ^ 3 * y ∈ A ↔ y ∈ A :=
    integral_unit_mul_mem_iff A (C.u ^ 3) y
  constructor
  · rintro ⟨hx, hy⟩
    have hx' := (variableChange_x_mem_iff A C x).mp hx
    refine ⟨hx', hm.mp ?_⟩
    simpa using A.sub_mem (A.sub_mem hy C.t.property) (hs hx')
  · rintro ⟨hx, hy⟩
    exact ⟨(variableChange_x_mem_iff A C x).mpr hx,
      A.toSubring.add_mem (A.toSubring.add_mem (hm.mpr hy) (hs hx)) C.t.property⟩

end FLT.Mazur
