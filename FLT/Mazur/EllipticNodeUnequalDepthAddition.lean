/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentInverse
public import FLT.Mazur.EllipticNodeSecantReduction

/-!
# Unequal nodal depths cannot add to smooth reduction

The shallower primitive point has unit divided x-coordinate. Its secant with
a deeper point is integral and reduces to a nodal tangent. The actual addition
formula therefore puts the sum above the node, outside E₀.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)

include D

/-- Two positive, distinct coordinate depths give a sum with singular reduction. -/
theorem not_smoothReduction_add_of_node_depth_lt (k j : ℕ) (hk : 0 < k) (hj : 0 < j)
    (hkn : k + j ≤ n / 2) (a b c d : A) (hp : IsUnit a ∨ IsUnit b)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ (k + j) * c : A) : K) ((π ^ (k + j) * d : A) : K)) :
    ¬ SmoothReduction A W (Affine.Point.toProjective (.some _ _ h₁ + .some _ _ h₂)) := by
  have he : W.toAffine.Equation (π ^ k * a) (π ^ k * b) :=
    (W.toAffine.map_equation (IsFractionRing.injective A K) _ _).mp h₁.1
  obtain ⟨ha, hb⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero
    D.maximalIdeal_eq n k hk (by omega) D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem a b hp he
  have hπ : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  obtain ⟨l, hl, hlr⟩ := exists_node_secant_slope hπ ha j hj b c d
  have hs := node_secant_slope_eq A W D.uniformizer_ne_zero hπ ha k j hj b c d l hl
  have hden : π ^ k * a ≠ π ^ (k + j) * c := by
    intro heq
    have hz : π ^ k * (a - π ^ j * c) = 0 := by
      rw [mul_sub, ← mul_assoc, ← pow_add, heq, sub_self]
    exact mul_ne_zero (pow_ne_zero k D.uniformizer_ne_zero)
      (node_secant_denominator_unit hπ ha j hj c).ne_zero hz
  have ht : residue A b * (residue A b + residue A W.a₁ * residue A a) = 0 := by
    rcases hb with ⟨hb, _⟩ | ⟨_, hb⟩
    · rw [(residue_eq_zero_iff _).mpr hb, zero_mul]
    · have hz := (residue_eq_zero_iff _).mpr hb
      simp only [map_add, map_mul] at hz
      rw [hz, mul_zero]
  have hmem (i : ℕ) (hi : 0 < i) (e : A) : π ^ i * e ∈ maximalIdeal A :=
    (maximalIdeal A).mul_mem_right e
      (Ideal.pow_le_self (Nat.ne_of_gt hi) (Ideal.pow_mem_pow hπ i))
  exact not_smoothReduction_add_of_node_slope A W _ _ _ _ l h₁ h₂
    (fun h => hden (Subtype.ext h.1)) hs D.a₂_mem
    (Ideal.pow_le_self (by omega) D.a₃_mem) (Ideal.pow_le_self (by omega) D.a₄_mem)
    (Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem)
    (hmem k hk a) (hmem k hk b) (hmem (k + j) (by omega) c)
    (node_secant_residue_tangent W ha hlr ht)

omit [DecidableEq K] in
/-- The unequal-depth obstruction applies to coordinate witnesses of actual generic points. -/
theorem NodePointCoordinates.not_smooth_add
    {P Q : (W.map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 0 < v.depth) (hvw : v.depth < w.depth) (hw : w.depth ≤ n / 2) :
    ¬ SmoothReduction A W (P + Q) := by
  classical
  have he : w.depth = v.depth + (w.depth - v.depth) := by omega
  have h := not_smoothReduction_add_of_node_depth_lt D v.depth (w.depth - v.depth) hv
    (by omega) (by omega) v.a v.b w.a w.b v.primitive v.nonsingular
    (by simpa only [← he] using w.nonsingular)
  rw [toProjective_add] at h
  simpa only [← he, ← v.represents, ← w.represents] using h

omit [DecidableEq K] in
/-- Positive unequal depths represent distinct classes in the actual quotient E/E₀. -/
theorem NodePointCoordinates.component_ne
    {P Q : (W.map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 0 < v.depth) (hvw : v.depth < w.depth) (hw : w.depth ≤ n / 2) :
    ellipticComponentHom A W P ≠ ellipticComponentHom A W Q := by
  obtain ⟨w', hw', _⟩ := exists_nodePointCoordinates_inverse D w hw
  have hn := v.not_smooth_add D w' hv (by omega) (by omega)
  intro he
  apply hn
  simpa only [sub_eq_add_neg] using (ellipticComponentHom_eq_iff A W P Q).mp he

end FLT.Mazur
