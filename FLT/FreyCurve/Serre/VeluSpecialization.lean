/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluFunctionField
public import Mathlib.Order.Filter.Cofinite

/-!
# Specialization of the quadratic function field at affine points

Rational coordinates regular at an abscissa form a subring of the quadratic
function field. At a point on the curve, evaluation of these coordinates is a
ring homomorphism. This supplies a specialization interface for the generic
Vélu identities; it does not assert regularity of their denominators.
-/

@[expose] public section

namespace RatFunc
variable {K : Type*} [Field K]

/-- The inverse of a regular function with nonzero value is regular. -/
theorem regularAt_inv_of_eval_ne_zero {x : K} {f : K⟮X⟯}
    (hv : eval (RingHom.id K) x f ≠ 0) : RegularAt x f⁻¹ := by
  have hf0 : f ≠ 0 := by intro h; simp [h] at hv
  apply RegularAt.of_dvd x (denom_inv_dvd hf0)
  intro hn
  apply hv
  simp [eval, Polynomial.eval₂_id, hn]

/-- Evaluation respects multiplication of regular functions. -/
theorem RegularAt.eval_mul {x : K} {f g : K⟮X⟯}
    (hf : RegularAt x f) (hg : RegularAt x g) :
    eval (RingHom.id K) x (f * g) =
      eval (RingHom.id K) x f * eval (RingHom.id K) x g :=
  RatFunc.eval_mul (RingHom.id K) x
    (by simpa only [RegularAt, Polynomial.eval₂_id] using hf)
    (by simpa only [RegularAt, Polynomial.eval₂_id] using hg)

/-- A regular function's nonzero value specializes its inverse. -/
theorem RegularAt.eval_inv {x : K} {f : K⟮X⟯} (hf : RegularAt x f)
    (hv : eval (RingHom.id K) x f ≠ 0) :
    eval (RingHom.id K) x f⁻¹ = (eval (RingHom.id K) x f)⁻¹ := by
  have hf0 : f ≠ 0 := by intro h; simp [h] at hv
  apply mul_left_cancel₀ hv
  rw [← hf.eval_mul (regularAt_inv_of_eval_ne_zero hv), mul_inv_cancel₀ hf0, eval_one,
    mul_inv_cancel₀ hv]

/-- Every rational function is regular outside a finite set of abscissae. -/
theorem eventually_regularAt (f : K⟮X⟯) :
    ∀ᶠ x in Filter.cofinite, RegularAt x f :=
  Polynomial.eventually_eval_ne_zero_cofinite f.denom_ne_zero

end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K)

/-- The two rational components have no pole at the specified abscissa. -/
def RegularAtAffine (x : K) (z : FunctionField E) : Prop :=
  RegularAt x z.re ∧ RegularAt x z.im

/-- The completed cubic is regular, with its expected value, at every abscissa. -/
theorem regular_eval_cubicFunction (x : K) :
    RegularAt x (cubicFunction E) ∧
      eval (RingHom.id K) x (cubicFunction E) =
        4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ := by
  constructor
  · have h := regularAt_div_polynomial x E.twoTorsionPolynomial.toPoly 1 (by simp)
    simpa [cubicFunction] using h
  · rw [cubicFunction, eval_algebraMap]
    simp [twoTorsionPolynomial, Cubic.toPoly]

/-- Componentwise regularity is preserved by sums. -/
theorem RegularAtAffine.add {x : K} {z w : FunctionField E}
    (hz : RegularAtAffine E x z) (hw : RegularAtAffine E x w) :
    RegularAtAffine E x (z + w) := ⟨hz.1.add hw.1, hz.2.add hw.2⟩

/-- Componentwise regularity is preserved by negation. -/
theorem RegularAtAffine.neg {x : K} {z : FunctionField E}
    (hz : RegularAtAffine E x z) : RegularAtAffine E x (-z) :=
  ⟨hz.1.neg, hz.2.neg⟩

/-- Componentwise regularity is preserved by products. -/
theorem RegularAtAffine.mul {x : K} {z w : FunctionField E}
    (hz : RegularAtAffine E x z) (hw : RegularAtAffine E x w) :
    RegularAtAffine E x (z * w) := by
  constructor
  · exact (hz.1.mul hw.1).add (((regular_eval_cubicFunction E x).1.mul hz.2).mul hw.2)
  · simpa only [QuadraticAlgebra.im_mul, zero_mul, add_zero] using
      (hz.1.mul hw.2).add (hz.2.mul hw.1)

/-- The subring on which affine specialization is defined componentwise. -/
def affineRegularSubring (x : K) : Subring (FunctionField E) where
  carrier := RegularAtAffine E x
  zero_mem' := by constructor <;> simpa using RegularAt.C x (0 : K)
  one_mem' := by
    constructor
    · change RegularAt x (1 : K⟮X⟯)
      simpa using RegularAt.C x (1 : K)
    · change RegularAt x (0 : K⟮X⟯)
      simpa using RegularAt.C x (0 : K)
  add_mem' := RegularAtAffine.add E
  mul_mem' := RegularAtAffine.mul E
  neg_mem' := RegularAtAffine.neg E

/-- Specialization substitutes the completed y-coordinate for the quadratic generator. -/
noncomputable def affineValue (x y : K) (z : FunctionField E) : K :=
  eval (RingHom.id K) x z.re +
    eval (RingHom.id K) x z.im * (2 * y + E.a₁ * x + E.a₃)

/-- Specialization is additive where both components are regular. -/
theorem affineValue_add (x y : K) {z w : FunctionField E}
    (hz : RegularAtAffine E x z) (hw : RegularAtAffine E x w) :
    affineValue E x y (z + w) = affineValue E x y z + affineValue E x y w := by
  simp only [affineValue, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    hz.1.eval_add hw.1, hz.2.eval_add hw.2]
  ring

/-- Specialization is multiplicative at a point satisfying the curve equation. -/
theorem affineValue_mul {x y : K} (hP : E.toAffine.Equation x y)
    {z w : FunctionField E}
    (hz : RegularAtAffine E x z) (hw : RegularAtAffine E x w) :
    affineValue E x y (z * w) = affineValue E x y z * affineValue E x y w := by
  have hF := regular_eval_cubicFunction E x
  have hs : (2 * y + E.a₁ * x + E.a₃) ^ 2 =
      4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ := by
    have hp := (Affine.equation_iff _ _).mp hP
    dsimp [b₂, b₄, b₆]
    linear_combination 4 * hp
  simp only [affineValue, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    zero_mul, add_zero, (hz.1.mul hw.1).eval_add ((hF.1.mul hz.2).mul hw.2),
    (hz.1.mul hw.2).eval_add (hz.2.mul hw.1), hz.1.eval_mul hw.1,
    (hF.1.mul hz.2).eval_mul hw.2, hF.1.eval_mul hz.2, hz.1.eval_mul hw.2,
    hz.2.eval_mul hw.1, hF.2]
  linear_combination -(eval (RingHom.id K) x z.im * eval (RingHom.id K) x w.im) * hs

/-- Evaluation on the componentwise regular subring is a ring homomorphism. -/
noncomputable def affineEval {x y : K} (hP : E.toAffine.Equation x y) :
    affineRegularSubring E x →+* K where
  toFun z := affineValue E x y z.val
  map_zero' := by simp [affineValue]
  map_one' := by
    change eval (RingHom.id K) x 1 + eval (RingHom.id K) x 0 * _ = 1
    simp
  map_add' z w := affineValue_add E x y z.property w.property
  map_mul' z w := affineValue_mul E hP z.property w.property

/-- A rational lift is regular precisely when its rational coordinate is regular. -/
theorem regularAtAffine_liftX (x : K) (f : K⟮X⟯) :
    RegularAtAffine E x (liftX E f) ↔ RegularAt x f := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by
      change RegularAt x (0 : K⟮X⟯)
      simpa using RegularAt.C x (0 : K)⟩

/-- Affine specialization of a rational lift is ordinary rational evaluation. -/
@[simp] theorem affineValue_liftX (x y : K) (f : K⟮X⟯) :
    affineValue E x y (liftX E f) = eval (RingHom.id K) x f := by
  simp [affineValue, liftX]

/-- Base-field constants retain their value under affine specialization. -/
@[simp] theorem affineValue_constant (x y c : K) :
    affineValue E x y (algebraMap K (FunctionField E) c) = c := by
  simp [affineValue]

/-- Any fixed function-field element has regular components outside a finite set. -/
theorem eventually_regularAtAffine (z : FunctionField E) :
    ∀ᶠ x in Filter.cofinite, RegularAtAffine E x z :=
  (eventually_regularAt z.re).and (eventually_regularAt z.im)

variable [CharZero K]

/-- Specialization of the lifted ordinate recovers the completed-coordinate formula. -/
theorem affineValue_liftY (E' : WeierstrassCurve K) (x y : K) (f g : K⟮X⟯)
    (hf : RegularAt x f) (hg : RegularAt x g) :
    affineValue E x y (liftY E E' f g) =
      (eval (RingHom.id K) x g * (2 * y + E.a₁ * x + E.a₃) -
        E'.a₁ * eval (RingHom.id K) x f - E'.a₃) / 2 := by
  have hr : (liftY E E' f g).re = C (-E'.a₁ / 2) * f + C (-E'.a₃ / 2) := by
    simp only [liftY, map_div₀, map_neg, map_ofNat]
    ring
  have hi : (liftY E E' f g).im = C (1 / 2 : K) * g := by
    simp only [liftY, map_div₀, map_one, map_ofNat]
    ring
  simp only [affineValue, hr, hi,
    ((RegularAt.C x (-E'.a₁ / 2)).mul hf).eval_add (RegularAt.C x (-E'.a₃ / 2)),
    (RegularAt.C x (-E'.a₁ / 2)).eval_mul hf,
    (RegularAt.C x (1 / 2 : K)).eval_mul hg, eval_C, RingHom.id_apply]
  ring

/-- The lifted generic Vélu coordinates specialize to the actual coordinate sums. -/
theorem affineValue_velu [DecidableEq K] (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) {x y : K}
    (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G) :
    affineValue E x y (liftX E (xFunction E G)) = xMap E G (.some x y hP) ∧
      affineValue E x y (liftY E (curve E G) (xFunction E G) (slopeFunction E G)) =
        yMap E G (.some x y hP) := by
  have hx := x_not_mem_kernelAbscissae E G hP hPG
  have hf := regular_eval_xFunction E G x hx
  have hg := regular_eval_slopeFunction E G x hx
  have hxf : eval (RingHom.id K) x (xFunction E G) = xMap E G (.some x y hP) := by
    rw [hf.2, xMap_eq_sum_abscissae E G hodd hP hPG]
  have hxg : eval (RingHom.id K) x (slopeFunction E G) = slopeFactor E G x := by
    rw [hg.2, slopeFactor_eq_sum_abscissae E G hodd x]
  refine ⟨by simpa using hxf, ?_⟩
  rw [affineValue_liftY E (curve E G) x y _ _ hf.1 hg.1, hxf, hxg]
  have hc := completed_yMap E G hP hPG
  change (slopeFactor E G x * (2 * y + E.a₁ * x + E.a₃) -
    E.a₁ * xMap E G (.some x y hP) - E.a₃) / 2 = _
  linear_combination -hc / 2

/-- An inverse specializes correctly whenever both it and the function are regular. -/
theorem affineValue_inv {x y : K} (hP : E.toAffine.Equation x y)
    {z : FunctionField E} (hz : RegularAtAffine E x z)
    (hzi : RegularAtAffine E x z⁻¹) :
    affineValue E x y z⁻¹ = (affineValue E x y z)⁻¹ := by
  by_cases hz0 : z = 0
  · simp [hz0, affineValue]
  · have hh := affineValue_mul E hP hz hzi
    rw [mul_inv_cancel₀ hz0] at hh
    have h1 : affineValue E x y 1 = 1 := by
      change eval (RingHom.id K) x 1 + eval (RingHom.id K) x 0 * _ = 1
      simp
    rw [h1] at hh
    have hv : affineValue E x y z ≠ 0 := by
      intro hv
      simp [hv] at hh
    apply mul_left_cancel₀ hv
    rw [← hh, mul_inv_cancel₀ hv]

/-- A nonzero function-field element has nonzero values off a finite set of abscissae.
The exceptional set works simultaneously for both points above each abscissa. -/
theorem eventually_affineValue_ne_zero {z : FunctionField E} (hz : z ≠ 0) :
    ∀ᶠ x in Filter.cofinite, ∀ y, E.toAffine.Equation x y → affineValue E x y z ≠ 0 := by
  filter_upwards [eventually_regularAtAffine E z, eventually_regularAtAffine E z⁻¹] with
    x hx hxi y hP
  have hh := affineValue_mul E hP hx hxi
  rw [mul_inv_cancel₀ hz] at hh
  intro hv
  rw [hv, zero_mul] at hh
  have h1 : affineValue E x y 1 = 1 := by
    change eval (RingHom.id K) x 1 + eval (RingHom.id K) x 0 * _ = 1
    simp
  exact one_ne_zero (h1.symm.trans hh)

/-- Inversion specializes outside a finite set, uniformly in the ordinate. -/
theorem eventually_affineValue_inv (z : FunctionField E) :
    ∀ᶠ x in Filter.cofinite, ∀ y, E.toAffine.Equation x y →
      affineValue E x y z⁻¹ = (affineValue E x y z)⁻¹ := by
  filter_upwards [eventually_regularAtAffine E z, eventually_regularAtAffine E z⁻¹] with
    x hx hxi y hP
  exact affineValue_inv E hP hx hxi

end WeierstrassCurve.Velu

namespace Function
variable {A B : Type*} [AddGroup A] [Infinite A] [AddLeftCancelSemigroup B]

/-- An addition law holding outside finitely many first summands holds everywhere.
An auxiliary summand avoids the three exceptional sets needed for associativity. -/
theorem map_add_of_cofinite (f : A → B)
    (h : ∀ Q, ∀ᶠ P in Filter.cofinite, f (P + Q) = f P + f Q) (P Q : A) :
    f (P + Q) = f P + f Q := by
  have ht : Filter.Tendsto (fun R : A => R + P) Filter.cofinite Filter.cofinite :=
    (show Function.Injective (fun R : A => R + P) from
      fun _ _ h => add_right_cancel h).tendsto_cofinite
  obtain ⟨R, hR, hRP, hRQ⟩ := ((h (P + Q)).and ((ht.eventually (h Q)).and (h P))).exists
  apply add_left_cancel (a := f R)
  calc
    f R + f (P + Q) = f (R + (P + Q)) := hR.symm
    _ = f ((R + P) + Q) := by rw [add_assoc]
    _ = (f R + f P) + f Q := by rw [hRP, hRQ]
    _ = f R + (f P + f Q) := add_assoc _ _ _

end Function
