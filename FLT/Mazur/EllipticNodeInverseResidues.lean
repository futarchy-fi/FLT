/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentInverse

/-!
# Original Laurent residues under arithmetic inversion

Every primitive witness for the actual inverse has the same horizontal
coordinate and the negative opposite tangent residue. These identities retain
the original parameters, including on the even middle component.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P : (W.map (algebraMap A K)).toProjective.Point}

include D

set_option backward.isDefEq.respectTransparency false in
/-- Inversion preserves depth and x, and negates the opposite tangent character. -/
theorem node_inverse_coordinate_residues
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π (-P))
    (hv : v.depth ≤ n / 2) :
    w.depth = v.depth ∧ w.a = v.a ∧
      residue A w.b = -residue A (v.b + W.a₁ * v.a) := by
  classical
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D v hv
  have hw := (w.unique D.uniformizer_ne_zero D.maximalIdeal_eq w').1.trans hw'
  obtain ⟨c, hc, hce⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
  have he : Affine.Point.some _ _ w.nonsingular = -(Affine.Point.some _ _ v.nonsingular) := by
    apply (Projective.Point.toAffineAddEquiv
      (W.map (algebraMap A K)).toProjective).symm.injective
    change (Affine.Point.some _ _ w.nonsingular).toProjective =
      (-(Affine.Point.some _ _ v.nonsingular)).toProjective
    rw [toProjective_neg, ← v.represents, ← w.represents]
  rw [Affine.Point.neg_some] at he
  obtain ⟨hx, hy⟩ := Affine.Point.some.inj he
  have hxa : w.a = v.a := by
    apply mul_left_cancel₀ (pow_ne_zero v.depth D.uniformizer_ne_zero)
    simpa only [hw] using Subtype.ext hx
  have hyA : π ^ v.depth * w.b = -(π ^ v.depth * v.b) -
      W.a₁ * (π ^ v.depth * v.a) - W.a₃ := by
    simp only [Affine.negY, map_a₁, map_a₃, ValuationSubring.algebraMap_apply, hw] at hy
    exact_mod_cast hy
  have hyb : w.b = -v.b - W.a₁ * v.a - c := by
    apply mul_left_cancel₀ (pow_ne_zero v.depth D.uniformizer_ne_zero)
    rw [hce] at hyA
    linear_combination hyA
  refine ⟨hw, hxa, ?_⟩
  rw [hyb, map_sub, map_sub, map_neg, map_mul, (residue_eq_zero_iff _).mpr hc,
    sub_zero, map_add, map_mul]
  ring

/-- The other oriented character of the inverse is the negative original vertical residue. -/
theorem node_inverse_other_residue
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π (-P))
    (hv : v.depth ≤ n / 2) :
    residue A (w.b + W.a₁ * w.a) = -residue A v.b := by
  obtain ⟨_, hx, hy⟩ := node_inverse_coordinate_residues D v w hv
  rw [map_add, map_mul, hy, hx, map_add, map_mul]
  ring

end FLT.Mazur
