/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingChangeParameter
public import FLT.Mazur.NilpotentAlgebraAutomorphism

/-!
# Square-zero corrections on the full smoothing chart

When the coefficient annihilates the smoothing, multiply the left coordinate
by one plus that coefficient times any chart function. The right coordinate is
fixed. Negating the function gives the full inverse, including nilpotent terms.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (t e : R) (he : e ^ 2 = 0) (het : e * t = 0)
local notation "A" => ChartRing t
local notation "E" => algebraMap R A e
local notation "x" => leftCoordinate t
local notation "y" => rightCoordinate t

/-- A full node correction with its unchanged right coordinate. -/
def squareZeroShear (p : A) : A →ₐ[R] A :=
  evaluate t (x + E * x * p) y (by
    rw [add_mul, coordinate_relation]
    have hz : E * algebraMap R A t = 0 := by rw [← map_mul, het, map_zero]
    rw [show E * x * p * y = (E * (x * y)) * p by ring,
      coordinate_relation, hz, zero_mul, add_zero])

/-- The complete left coordinate, including its correction. -/
@[simp] theorem squareZeroShear_left (p : A) :
    squareZeroShear t e het p x = x + E * x * p := evaluate_left ..

/-- The other coordinate remains fixed on the whole node. -/
@[simp] theorem squareZeroShear_right (p : A) :
    squareZeroShear t e het p y = y := evaluate_right ..

/-- All chart functions change by an element of the original scalar ideal. -/
theorem squareZeroShear_sub_mem (p z : A) :
    squareZeroShear t e het p z - z ∈ (Ideal.span {e}).map (algebraMap R A) := by
  let J := (Ideal.span {e}).map (algebraMap R A)
  let q := Ideal.Quotient.mkₐ R J
  have hE : q E = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton e)))
  have hq : q.comp (squareZeroShear t e het p) = q := by
    refine chartRing_hom_ext (S := A ⧸ J) t (q.comp (squareZeroShear t e het p)) q ?_ ?_
    · simp only [AlgHom.comp_apply, squareZeroShear_left, map_add, map_mul, hE]
      change (q x : A ⧸ J) + 0 * q x * q p = q x
      exact (congrArg (fun v : A ⧸ J ↦ q x + v * q p) (zero_mul (q x))).trans
        ((congrArg (fun v : A ⧸ J ↦ q x + v) (zero_mul (q p))).trans (add_zero (q x)))
    · simp only [AlgHom.comp_apply, squareZeroShear_right]
  exact Ideal.Quotient.eq.mp (DFunLike.congr_fun hq z)

include he

/-- The square-zero scalar removes the entire correction on every chart function. -/
theorem squareZeroShear_weighted (p z : A) : E * squareZeroShear t e het p z = E * z := by
  have h := squareZeroShear_sub_mem t e het p z
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h
  obtain ⟨w, hw⟩ := h
  apply sub_eq_zero.mp
  rw [← mul_sub, hw, ← mul_assoc, ← map_mul, ← pow_two, he, map_zero, zero_mul]

/-- These full node corrections compose by addition of their chart functions. -/
theorem squareZeroShear_comp (p q : A) :
    (squareZeroShear t e het p).comp (squareZeroShear t e het q) =
      squareZeroShear t e het (p + q) := by
  apply chartRing_hom_ext t
  · simp only [AlgHom.comp_apply, squareZeroShear_left, map_add, map_mul, AlgHom.commutes]
    have hx := squareZeroShear_weighted t e he het p x
    have hq := squareZeroShear_weighted t e he het p q
    simp only [squareZeroShear_left] at hx
    calc
      _ = x + E * x * p + (E * squareZeroShear t e het p q) * x := by
        rw [show E * (x + E * x * p) * squareZeroShear t e het p q =
          (E * (x + E * x * p)) * squareZeroShear t e het p q by rfl, hx]
        ring
      _ = _ := by rw [hq]; ring
  · simp only [AlgHom.comp_apply, squareZeroShear_right]

omit he in
/-- The zero correction is the identity on the entire node. -/
@[simp] theorem squareZeroShear_zero : squareZeroShear t e het (0 : A) = AlgHom.id R A := by
  apply chartRing_hom_ext t <;> simp

/-- The inverse is the same correction with its full chart function negated. -/
def squareZeroShearEquiv (p : A) : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (squareZeroShear t e het p) (squareZeroShear t e het (-p))
    (by rw [squareZeroShear_comp t e he, add_neg_cancel, squareZeroShear_zero])
    (by rw [squareZeroShear_comp t e he, neg_add_cancel, squareZeroShear_zero])

end FLT.Mazur.PolygonSmoothing
