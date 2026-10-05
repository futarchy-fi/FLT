/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeBranchInverse
public import FLT.Mazur.EllipticReductionRelation

/-!
# Primitive nodal coordinates of actual generic points

A coordinate witness consists of a primitive factorization and an equality
with the actual projective point. Singular reduction forces an integral affine
chart, where the finite-depth equation supplies such a witness.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Primitive scaled affine coordinates representing an actual generic point. -/
structure NodePointCoordinates (π : A) (P : (W.map (algebraMap A K)).toProjective.Point) where
  /-- The common power of the uniformizer. -/
  depth : ℕ
  /-- The divided x-coordinate. -/
  a : A
  /-- The divided y-coordinate. -/
  b : A
  primitive : IsUnit a ∨ IsUnit b
  nonsingular : (W.map (algebraMap A K)).toAffine.Nonsingular
    ((π ^ depth * a : A) : K) ((π ^ depth * b : A) : K)
  represents : P = Affine.Point.toProjective (.some _ _ nonsingular)

variable {A W} {π : A} {P : (W.map (algebraMap A K)).toProjective.Point}

/-- The integral coordinates satisfy the original equation, by injectivity into the field. -/
theorem NodePointCoordinates.equation (v : NodePointCoordinates A W π P) :
    W.toAffine.Equation (π ^ v.depth * v.a) (π ^ v.depth * v.b) :=
  (W.toAffine.map_equation (IsFractionRing.injective A K) _ _).mp v.nonsingular.1

set_option backward.isDefEq.respectTransparency false in
/-- Two witnesses for the same actual point have the same depth and quotients. -/
theorem NodePointCoordinates.unique (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) (v w : NodePointCoordinates A W π P) :
    v.depth = w.depth ∧ v.a = w.a ∧ v.b = w.b := by
  classical
  have he : Affine.Point.some _ _ v.nonsingular = Affine.Point.some _ _ w.nonsingular := by
    apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.map (algebraMap A K)).toProjective).symm.injective
    exact v.represents.symm.trans w.represents
  obtain ⟨hx, hy⟩ := Affine.Point.some.inj he
  exact node_primitive_coordinates_unique hπ hgen v.primitive w.primitive
    (Subtype.ext hx) (Subtype.ext hy)

/-- A coordinate witness has smooth reduction precisely at depth zero. -/
theorem NodePointCoordinates.smooth_iff (hπm : π ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A) (v : NodePointCoordinates A W π P) :
    SmoothReduction A W P ↔ v.depth = 0 := by
  conv_lhs => rw [v.represents]
  rw [smoothReduction_affine_iff]
  exact node_scaled_nonsingular_iff_depth_zero W hπm h3 h4 h6
    v.depth v.a v.b v.primitive v.equation

variable (A W)

set_option backward.isDefEq.respectTransparency false in
/-- Every point outside E₀ has bounded primitive nodal coordinates. -/
theorem exists_nodePointCoordinates (π : A) (hgen : maximalIdeal A = Ideal.span {π})
    (n : ℕ) (h3 : W.a₃ ∈ maximalIdeal A ^ (n + 1))
    (h4 : W.a₄ ∈ maximalIdeal A ^ (n + 1)) (h6 : W.a₆ ∉ maximalIdeal A ^ (n + 1))
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    ∃ v : NodePointCoordinates A W π P, v.depth ≤ n / 2 := by
  classical
  obtain ⟨p, rfl⟩ := (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W.map (algebraMap A K)).toProjective).symm.surjective P
  cases p with
  | zero => exact (hP (smoothReduction_zero A W)).elim
  | @some x y h =>
    have hi : x ∈ A ∧ y ∈ A := by
      by_contra hn
      exact hP (smoothReduction_of_nonintegral A W h hn)
    let u : A := ⟨x, hi.1⟩
    let v : A := ⟨y, hi.2⟩
    have he : W.toAffine.Equation u v :=
      (W.toAffine.map_equation (IsFractionRing.injective A K) u v).mp h.1
    obtain ⟨k, hk, a, b, hx, hy, hp⟩ :=
      exists_node_point_coordinates W hgen he n h3 h4 h6
    have hs : (W.map (algebraMap A K)).toAffine.Nonsingular
        ((π ^ k * a : A) : K) ((π ^ k * b : A) : K) := by
      simpa only [← hx, ← hy] using h
    refine ⟨⟨k, a, b, hp, hs, ?_⟩, hk⟩
    change (Affine.Point.some x y h).toProjective = _
    apply congrArg Affine.Point.toProjective
    simp only [Affine.Point.some.injEq]
    exact ⟨congrArg Subtype.val hx, congrArg Subtype.val hy⟩

end FLT.Mazur
