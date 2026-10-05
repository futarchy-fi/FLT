/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticReductionInfinityChart
public import FLT.EllipticCurve.PointReductionKernel

/-!
# Affine points related by projective reduction

This relation uses the actual projective reduction, including at bad reduction.
Its target consists of smooth special-fiber points, so singular reductions have
no related target. No additive closure is used in its definition.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- An actual generic affine point reduces to the specified smooth special point. -/
def ReducesTo (P : (W.map (algebraMap A K)).toAffine.Point)
    (p : (W.map (residue A)).toAffine.Point) : Prop :=
  projectiveReduction A W P.toProjective = p.toProjective.point

/-- Passing from affine to projective points preserves addition. -/
theorem toProjective_add {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
    (P Q : E.toAffine.Point) : (P + Q).toProjective = P.toProjective + Q.toProjective := by
  classical
  exact (Point.toAffineAddEquiv E.toProjective).symm.map_add P Q

/-- Passing from affine to projective points preserves negation. -/
theorem toProjective_neg {F : Type*} [Field F] (E : WeierstrassCurve F)
    (P : E.toAffine.Point) : (-P).toProjective = -P.toProjective := by
  classical
  exact (Point.toAffineAddEquiv E.toProjective).symm.map_neg P

/-- A generic point has at most one smooth reduced point. -/
theorem ReducesTo.unique {P : (W.map (algebraMap A K)).toAffine.Point}
    {p q : (W.map (residue A)).toAffine.Point}
    (hp : ReducesTo A W P p) (hq : ReducesTo A W P q) : p = q := by
  classical
  apply (Point.toAffineAddEquiv (W.map (residue A)).toProjective).symm.injective
  exact Point.ext (hp.symm.trans hq)

/-- The identity reduces to the identity. -/
theorem reducesTo_zero : ReducesTo A W 0 0 := projectiveReduction_zero A W

/-- Reduction to the identity is the infinity-fiber condition. -/
theorem reducesTo_zero_iff (P : (W.map (algebraMap A K)).toAffine.Point) :
    ReducesTo A W P 0 ↔ InfinityReduction A W P.toProjective := Iff.rfl

/-- Reduction of integral affine coordinates. -/
theorem reducesTo_integral (x y : A)
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular (x : K) (y : K))
    (hr : (W.map (residue A)).toAffine.Nonsingular (residue A x) (residue A y)) :
    ReducesTo A W (.some _ _ h) (.some _ _ hr) := projectiveReduction_affine A W x y h

/-- Nonintegral x-coordinates force reduction to infinity. -/
theorem reducesTo_of_nonintegral {x y : K}
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular x y) (hx : x ∉ A) :
    ReducesTo A W (.some _ _ h) 0 :=
  (infinityReduction_affine_iff A W h).mpr (fun hi => hx hi.1)

/-- An affine point reducing to infinity cannot have integral x-coordinate. -/
theorem ReducesTo.not_mem_x {x y : K}
    {h : (W.map (algebraMap A K)).toAffine.Nonsingular x y}
    (hp : ReducesTo A W (.some _ _ h) 0) : x ∉ A := by
  intro hx
  exact (infinityReduction_affine_iff A W h).mp hp ⟨hx, W.mem_y_of_mem_x A h.1 hx⟩

/-- The relation is preserved by negation. -/
theorem ReducesTo.neg {P : (W.map (algebraMap A K)).toAffine.Point}
    {p : (W.map (residue A)).toAffine.Point} (hp : ReducesTo A W P p) :
    ReducesTo A W (-P) (-p) := by
  unfold ReducesTo at *
  rw [toProjective_neg, projectiveReduction_neg, hp, toProjective_neg, Point.neg_point]

/-- Existence of a related point is exactly nonsingular projective reduction. -/
theorem exists_reducesTo_iff (P : (W.map (algebraMap A K)).toAffine.Point) :
    (∃ p, ReducesTo A W P p) ↔ SmoothReduction A W P.toProjective := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    change (W.map (residue A)).toProjective.NonsingularLift _
    rw [show projectiveReduction A W P.toProjective = _ from hp]
    exact p.toProjective.nonsingular
  · intro hp
    let p : (W.map (residue A)).toProjective.Point := ⟨hp⟩
    refine ⟨(Point.toAffineAddEquiv _ ) p, ?_⟩
    change projectiveReduction A W P.toProjective =
      ((Point.toAffineAddEquiv _).symm ((Point.toAffineAddEquiv _) p)).point
    rw [AddEquiv.symm_apply_apply]

end FLT.Mazur
