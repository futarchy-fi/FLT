/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeInverseParameter

/-!
# The original initial equation evaluated on a full arithmetic node

The inverse incidence parameter and the translated slope solve the entire
original equation. The node's original smoothing scale is retained.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
local notation "f" => algebraMap R S

include hr in
/-- Evaluation at any incidence value retains the original polynomial conic root. -/
theorem polynomialRoot_eval_equation (z : S) :
    r.eval₂ f z ^ 2 + (f W.a₁ + f b3 * z) * r.eval₂ f z =
      f W.a₂ + f b4 * z + f b6 * z ^ 2 := by
  have h := congrArg (fun g : R[X] ↦ g.eval₂ f z) hr
  simpa only [polynomialSlopeLinear, polynomialSlopeConstant, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_C, eval₂_X] using h

include hr in
/-- The translated slope reconstructs the full original horizontal function. -/
theorem polynomialRoot_eval_horizontal (z q : S) :
    (q + r.eval₂ f z) ^ 2 + (f W.a₁ + f b3 * z) * (q + r.eval₂ f z) -
      (f W.a₂ + f b4 * z + f b6 * z ^ 2) =
        q * (q + f W.a₁ + (r.eval₂ f z + r.eval₂ f z + f b3 * z)) := by
  have h := polynomialRoot_eval_equation W b3 b4 b6 r hr z
  linear_combination h

variable (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
  (p q : S) (hu : IsUnit (q + algebraMap R S W.a₁))
  (hpq : p * q = algebraMap R S s)
local notation "T" => polynomialNodeInverseT b3 r I hI hrI h3 W p q hu

include hr hu hpq in
/-- The independently constructed node coordinates satisfy the original initial equation. -/
theorem polynomialNodeInverse_incidence :
    T * ((q + r.eval₂ f T) ^ 2 + (f W.a₁ + f b3 * T) * (q + r.eval₂ f T) -
      (f W.a₂ + f b4 * T + f b6 * T ^ 2)) = f s := by
  have ht := polynomialNodeInverseT_equation b3 r I hI hrI h3 W p q hu
  rw [polynomialRoot_eval_horizontal W b3 b4 b6 r hr]
  linear_combination q * ht + hpq

/-- Evaluation of every original initial function on the full arithmetic node neighborhood. -/
def polynomialNodeEvaluation : Coordinate W s b3 b4 b6 →ₐ[R] S :=
  evaluation W s b3 b4 b6 T (q + r.eval₂ f T)
    (polynomialNodeInverse_incidence W s b3 b4 b6 r hr I hI hrI h3 p q hu hpq)

/-- The entire original incidence is the constructed inverse parameter. -/
@[simp] theorem polynomialNodeEvaluation_t :
    polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 p q hu hpq
      (t W s b3 b4 b6) = T := evaluation_t ..

/-- The original slope includes the full polynomial root correction. -/
@[simp] theorem polynomialNodeEvaluation_v :
    polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 p q hu hpq
      (v W s b3 b4 b6) = q + r.eval₂ f T := evaluation_v ..

end FLT.Mazur.WeierstrassModificationX
