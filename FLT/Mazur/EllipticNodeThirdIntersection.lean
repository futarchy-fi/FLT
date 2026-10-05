/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeAdditionCoordinates
public import FLT.Mazur.EllipticNodeLineProducts

/-!
# The third intersection is the negative of the actual sum

A coordinate witness for the negative sum has the addition x-coordinate
and lies on the original secant or tangent. This connects the polynomial
line-intersection identities to actual projective group addition.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A}
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

set_option backward.isDefEq.respectTransparency false in
/-- Coordinates of the negative actual sum give the third point on the addition line. -/
theorem node_third_intersection_coordinates
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (-(P + Q))) (l : A)
    (hxy : ¬ (((π ^ v.depth * v.a : A) : K) = ((π ^ w.depth * w.a : A) : K) ∧
      ((π ^ v.depth * v.b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ w.depth * w.a : A) : K) ((π ^ w.depth * w.b : A) : K)))
    (hl : (W.map (algebraMap A K)).toAffine.slope
      ((π ^ v.depth * v.a : A) : K) ((π ^ w.depth * w.a : A) : K)
      ((π ^ v.depth * v.b : A) : K) ((π ^ w.depth * w.b : A) : K) = (l : K)) :
    π ^ u.depth * u.a = W.toAffine.addX (π ^ v.depth * v.a) (π ^ w.depth * w.a) l ∧
      π ^ u.depth * u.b - l * (π ^ u.depth * u.a) =
        π ^ v.depth * v.b - l * (π ^ v.depth * v.a) := by
  have he : Affine.Point.some _ _ u.nonsingular =
      -(Affine.Point.some _ _ v.nonsingular + Affine.Point.some _ _ w.nonsingular) := by
    apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.map (algebraMap A K)).toProjective).symm.injective
    change (Affine.Point.some _ _ u.nonsingular).toProjective =
      (-(Affine.Point.some _ _ v.nonsingular + Affine.Point.some _ _ w.nonsingular)).toProjective
    rw [toProjective_neg, toProjective_add, ← u.represents, ← v.represents, ← w.represents]
  rw [Affine.Point.add_some hxy, Affine.Point.neg_some] at he
  obtain ⟨hx, hy⟩ := Affine.Point.some.inj he
  rw [hl] at hx hy
  have hxA : π ^ u.depth * u.a = W.toAffine.addX (π ^ v.depth * v.a) (π ^ w.depth * w.a) l := by
    have hm := W.toAffine.map_addX (algebraMap A K)
      (π ^ v.depth * v.a) (π ^ w.depth * w.a) l
    change (W.map (algebraMap A K)).toAffine.addX _ _ _ = _ at hm
    simp only [ValuationSubring.algebraMap_apply] at hm
    rw [hm] at hx
    exact Subtype.ext hx
  refine ⟨hxA, ?_⟩
  have hyK : ((π ^ u.depth * u.b : A) : K) - (l : K) * ((π ^ u.depth * u.a : A) : K) =
      ((π ^ v.depth * v.b : A) : K) - (l : K) * ((π ^ v.depth * v.a : A) : K) := by
    simp only [Affine.negY, Affine.addY, Affine.negAddY] at hy
    linear_combination hy - (l : K) * hx
  exact_mod_cast hyK

end FLT.Mazur
