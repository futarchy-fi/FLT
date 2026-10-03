/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPowerNodeEndpoints
public import FLT.Mazur.PolygonPolynomialMatching
/-!
# Predecessor weights for common-node matching

The pinching convention identifies zero on i with infinity on next(i).
Reindexing the checked common-node equality therefore gives the predecessor
weight (-a(pred(i)))^(-m). For positive powers the result is precisely the
existing bounded-polynomial matching predicate, including n=1 and n=2.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonPowerNodeEndpoints
open FCurve PolygonPinching ProjectiveLineMarkedHZero
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (m : ℕ)

/-- The predecessor-oriented weight for the actual marked divisor power. -/
def weight (i : Fin n) : K := ((-(a ((finRotate n).symm i) : K)) ^ m)⁻¹

omit [NeZero n] in
/-- Every matching weight is nonzero. -/
lemma weight_ne_zero (i : Fin n) : weight K n a m i ≠ 0 :=
  inv_ne_zero (pow_ne_zero m (neg_ne_zero.mpr (Units.ne_zero _)))

omit [NeZero n] in
/-- Reindex normalized node equations without any dependent H0 transport. -/
lemma polynomial_predecessor_iff (P : Fin n → Polynomial K) :
    (∀ i, (P i).eval 0 / (-(a i : K)) ^ m = (P (next hn i)).coeff m) ↔
      ∀ i, (P i).coeff m = weight K n a m i * (P ((finRotate n).symm i)).coeff 0 := by
  constructor
  · intro hx i
    have hi := hx ((finRotate n).symm i)
    rw [PolygonCyclicAtlas.next_eq_rotate, Equiv.apply_symm_apply] at hi
    simpa only [weight, Polynomial.coeff_zero_eq_eval_zero, div_eq_inv_mul] using hi.symm
  · intro hx i
    have hi := hx (next hn i)
    simpa only [weight, PolygonCyclicAtlas.next_eq_rotate, Equiv.symm_apply_apply,
      Polynomial.coeff_zero_eq_eval_zero, div_eq_inv_mul] using hi.symm

/-- Actual common-node matching uses the predecessor coefficient and weight. -/
lemma predecessor_matching_iff (x : ∀ i, H0 K (a i) m) :
    (∀ i, zeroValue K n hn p q h a m i (x i) =
      infinityValue K n hn p q h a m i (x (next hn i))) ↔
    ∀ i, (polynomialEquiv K (a i) m (x i)).val.coeff m =
      weight K n a m i *
        (polynomialEquiv K (a ((finRotate n).symm i)) m (x ((finRotate n).symm i))).val.coeff 0 :=
  (forall_congr' fun i ↦ matching_iff K n hn p q h a m i (x i) (x (next hn i))).trans
    (polynomial_predecessor_iff K n hn a m (fun i ↦ (polynomialEquiv K (a i) m (x i)).val))

/-- For positive powers, common-node matching is the existing polynomial predicate. -/
lemma polynomial_matching_iff (d : ℕ) (x : ∀ i, H0 K (a i) (d + 1)) :
    (∀ i, zeroValue K n hn p q h a (d + 1) i (x i) =
      infinityValue K n hn p q h a (d + 1) i (x (next hn i))) ↔
    (fun i ↦ polynomialEquiv K (a i) (d + 1) (x i)) ∈
      PolygonPolynomialMatching.matching (fun _ : Fin n ↦ d) (finRotate n).symm
        (weight K n a (d + 1)) := by
  rw [predecessor_matching_iff, PolygonPolynomialMatching.mem_matching]
end FLT.Mazur.PolygonPowerNodeEndpoints
