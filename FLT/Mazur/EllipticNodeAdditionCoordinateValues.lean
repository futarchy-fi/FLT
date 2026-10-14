/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeAdditionCoordinates

/-!
# Recovering the actual addition coordinates

Every primitive witness for a sum agrees with the integral addition formulas
when the actual secant or tangent slope is integral. This allows residue
computations on an arbitrary witness, without replacing the specialization map.
-/

@[expose] public section
namespace FLT.Mazur
open WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A}
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary witness for the actual sum has the integral addition coordinates. -/
theorem node_addition_coordinate_values
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q)) (l : A)
    (hxy : ¬ (((π ^ v.depth * v.a : A) : K) = ((π ^ w.depth * w.a : A) : K) ∧
      ((π ^ v.depth * v.b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ w.depth * w.a : A) : K) ((π ^ w.depth * w.b : A) : K)))
    (hl : (W.map (algebraMap A K)).toAffine.slope
      ((π ^ v.depth * v.a : A) : K) ((π ^ w.depth * w.a : A) : K)
      ((π ^ v.depth * v.b : A) : K) ((π ^ w.depth * w.b : A) : K) = (l : K)) :
    π ^ u.depth * u.a = W.toAffine.addX (π ^ v.depth * v.a) (π ^ w.depth * w.a) l ∧
      π ^ u.depth * u.b = W.toAffine.addY (π ^ v.depth * v.a) (π ^ w.depth * w.a)
        (π ^ v.depth * v.b) l := by
  have he : Affine.Point.some _ _ u.nonsingular =
      Affine.Point.some _ _ v.nonsingular + Affine.Point.some _ _ w.nonsingular := by
    apply (Projective.Point.toAffineAddEquiv
      (W.map (algebraMap A K)).toProjective).symm.injective
    change (Affine.Point.some _ _ u.nonsingular).toProjective =
      (Affine.Point.some _ _ v.nonsingular + Affine.Point.some _ _ w.nonsingular).toProjective
    rw [toProjective_add, ← u.represents, ← v.represents, ← w.represents]
  rw [Affine.Point.add_some hxy] at he
  obtain ⟨hx, hy⟩ := Affine.Point.some.inj he
  rw [hl] at hx hy
  have hxmap := W.toAffine.map_addX (algebraMap A K)
    (π ^ v.depth * v.a) (π ^ w.depth * w.a) l
  have hymap := W.toAffine.map_addY (algebraMap A K)
    (π ^ v.depth * v.a) (π ^ v.depth * v.b) (π ^ w.depth * w.a) l
  change (W.map (algebraMap A K)).toAffine.addX _ _ _ = _ at hxmap
  change (W.map (algebraMap A K)).toAffine.addY _ _ _ _ = _ at hymap
  simp only [ValuationSubring.algebraMap_apply] at hxmap hymap
  rw [hxmap] at hx
  rw [hymap] at hy
  exact ⟨Subtype.ext hx, Subtype.ext hy⟩

end FLT.Mazur
