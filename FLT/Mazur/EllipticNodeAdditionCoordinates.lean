/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodePointCoordinates
public import FLT.Mazur.EllipticNodeAdditionProduct

/-!
# Coordinate witnesses from the actual addition formulas

Primitive factors of the integral addition coordinates give a witness for
the sum in the generic projective group. The input slope is the actual
Weierstrass slope; nonsingularity follows from the generic addition theorem.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A}
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Turn primitive factors of the actual addition formulas into a coordinate witness. -/
theorem exists_nodePointCoordinates_add_of_factors
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (l : A) (k : ℕ) (a b : A) (hp : IsUnit a ∨ IsUnit b)
    (hxy : ¬ (((π ^ v.depth * v.a : A) : K) = ((π ^ w.depth * w.a : A) : K) ∧
      ((π ^ v.depth * v.b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ w.depth * w.a : A) : K) ((π ^ w.depth * w.b : A) : K)))
    (hl : (W.map (algebraMap A K)).toAffine.slope
      ((π ^ v.depth * v.a : A) : K) ((π ^ w.depth * w.a : A) : K)
      ((π ^ v.depth * v.b : A) : K) ((π ^ w.depth * w.b : A) : K) = (l : K))
    (hx : W.toAffine.addX (π ^ v.depth * v.a) (π ^ w.depth * w.a) l = π ^ k * a)
    (hy : W.toAffine.addY (π ^ v.depth * v.a) (π ^ w.depth * w.a)
      (π ^ v.depth * v.b) l = π ^ k * b) :
    ∃ u : NodePointCoordinates A W π (P + Q), u.depth = k ∧ u.a = a ∧ u.b = b := by
  have hxK := W.toAffine.map_addX (algebraMap A K)
    (π ^ v.depth * v.a) (π ^ w.depth * w.a) l
  have hyK := W.toAffine.map_addY (algebraMap A K)
    (π ^ v.depth * v.a) (π ^ v.depth * v.b) (π ^ w.depth * w.a) l
  change (W.map (algebraMap A K)).toAffine.addX _ _ _ = _ at hxK
  change (W.map (algebraMap A K)).toAffine.addY _ _ _ _ = _ at hyK
  rw [hx] at hxK
  rw [hy] at hyK
  simp only [ValuationSubring.algebraMap_apply] at hxK hyK
  have hn := Affine.nonsingular_add v.nonsingular w.nonsingular hxy
  rw [hl, hxK, hyK] at hn
  refine ⟨⟨k, a, b, hp, hn, ?_⟩, rfl, rfl, rfl⟩
  rw [v.represents, w.represents, ← toProjective_add, Affine.Point.add_some hxy]
  simp only [hl, hxK, hyK]

end FLT.Mazur
