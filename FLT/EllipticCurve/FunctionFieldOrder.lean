/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.MultiplicationRootExistence
/-!
# Translation and constant functions in terms of point orders

Point orders commute with translation and detect constant rational functions.
-/

@[expose] public section

open scoped nonZeroDivisors WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]

/-- Every point order is the infinity order after translation to that point. -/
theorem pointOrder_eq_translation (f : W.FunctionField) (P : W.Point) :
    pointOrder f P = -WithZero.log (infinityValuation W (translationPullback W P f)) := by
  cases P with
  | zero => rw [show (Point.zero : W.Point) = 0 from rfl, translationPullback_zero]; rfl
  | some x y h => rw [pointOrder_some, pointValuation_eq_translation]; rfl

/-- Translation transports the order to the translated point. -/
theorem pointOrder_translationPullback (f : W.FunctionField) (P Q : W.Point) :
    pointOrder (translationPullback W Q f) P = pointOrder f (P + Q) := by
  rw [pointOrder_eq_translation, pointOrder_eq_translation]
  exact congrArg (fun g => -WithZero.log (infinityValuation W g))
    (congrArg (fun φ : W.FunctionField →ₐ[F] W.FunctionField => φ f)
      (translationPullback_add W P Q))

omit [DecidableEq F] in
/-- A nonzero constant has order zero at every point. -/
theorem pointOrder_const {c : F} (hc : c ≠ 0) (P : W.Point) :
    pointOrder (algebraMap F W.FunctionField c) P = 0 := by
  classical
  rw [pointOrder_eq_translation, AlgHom.commutes,
    Valuation.IsTrivialOn.eq_one _ hc]
  simp

omit [DecidableEq F] in
/-- Orders of a power are the corresponding multiples of the order. -/
theorem pointOrder_pow {f : W.FunctionField} (hf : f ≠ 0) (n : ℕ) (P : W.Point) :
    pointOrder (f ^ n) P = n * pointOrder f P := by
  induction n with
  | zero => simpa using pointOrder_const W one_ne_zero P
  | succ n ih => rw [pow_succ, pointOrder_mul (pow_ne_zero n hf) hf, ih]; push_cast; ring

omit [DecidableEq F] in
/-- Orders add over finite products of nonzero functions. -/
theorem pointOrder_prod {ι : Type*} (s : Finset ι) (f : ι → W.FunctionField)
    (hf : ∀ i ∈ s, f i ≠ 0) (P : W.Point) :
    pointOrder (∏ i ∈ s, f i) P = ∑ i ∈ s, pointOrder (f i) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pointOrder_const W one_ne_zero P
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      pointOrder_mul (hf i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

omit [DecidableEq F] in
/-- A nonzero function with zero orders at all affine points is constant. -/
theorem exists_const_of_pointOrder_eq_zero {f : W.FunctionField} (hf : f ≠ 0)
    (h : ∀ P, pointOrder f P = 0) :
    ∃ c : F, c ≠ 0 ∧ algebraMap F W.FunctionField c = f := by
  have he : FractionalIdeal.spanSingleton W.CoordinateRing⁰ (1 : W.FunctionField) =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ f := by
    apply CoordinateRing.fractionalIdeal_ext
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr one_ne_zero)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf)
    intro x y hp
    change pointOrder (1 : W.FunctionField) (Point.some x y hp) = _
    rw [show (1 : W.FunctionField) = algebraMap F W.FunctionField 1 by simp,
      pointOrder_const W one_ne_zero]
    exact (h (Point.some x y hp)).symm
  obtain ⟨c, hc, he⟩ := exists_eq_const_mul_of_span_eq he
  exact ⟨c, hc, by simpa using he.symm⟩
end WeierstrassCurve.Affine.FunctionField
