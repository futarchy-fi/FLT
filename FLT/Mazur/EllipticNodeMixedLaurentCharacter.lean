/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeDifferenceCoordinates
public import FLT.Mazur.EllipticNodeAdditionCoordinateValues
public import FLT.Mazur.EllipticNodeDifferenceFactorResidues

/-!
# The original Laurent character of a mixed-branch sum

For unequal depths, a shallower first-branch point and a deeper unit vertical
coordinate give a sum at the depth difference. Its primitive coordinates
satisfy explicit residue identities, for any witness of the actual sum.
The deeper point may be on the even middle component.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Actual mixed-branch sums have the computed depth and original leading coefficients. -/
theorem node_add_first_unit_residues
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    u.depth = w.depth - v.depth ∧
      residue A v.a * residue A u.a = -residue A W.a₁ * residue A w.b ∧
      residue A u.b = -residue A W.a₁ * residue A u.a := by
  classical
  let k := v.depth
  let j := w.depth - v.depth
  have hj : 0 < j := by dsimp [j]; omega
  have he : w.depth = k + j := by dsimp [k, j]; omega
  obtain ⟨ha, _⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero
    D.maximalIdeal_eq n v.depth hk (by omega) D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    v.a v.b v.primitive v.equation
  have hπ : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  obtain ⟨l, hl, hlr⟩ := exists_node_secant_slope hπ ha j hj v.b w.a w.b
  have hl0 : residue A l = 0 := by
    rw [(residue_eq_zero_iff _).mpr hb] at hlr
    exact (mul_eq_zero.mp hlr).resolve_right ((residue_ne_zero_iff_isUnit _).mpr ha)
  have hs := node_secant_slope_eq A W D.uniformizer_ne_zero hπ ha k j hj v.b w.a w.b l hl
  have hden : π ^ k * v.a ≠ π ^ (k + j) * w.a := by
    intro hh
    have hz : π ^ k * (v.a - π ^ j * w.a) = 0 := by
      rw [mul_sub, ← mul_assoc, ← pow_add, hh, sub_self]
    exact mul_ne_zero (pow_ne_zero k D.uniformizer_ne_zero)
      (node_secant_denominator_unit hπ ha j hj w.a).ne_zero hz
  have hxy : ¬ (((π ^ k * v.a : A) : K) = ((π ^ (k + j) * w.a : A) : K) ∧
      ((π ^ k * v.b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ (k + j) * w.a : A) : K) ((π ^ (k + j) * w.b : A) : K)) :=
    fun h => hden (Subtype.ext h.1)
  obtain ⟨e₃, _, h3⟩ := exists_node_deep_factor D.maximalIdeal_eq (k + j)
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
  obtain ⟨e₄, he₄, h4⟩ := exists_node_deep_factor D.maximalIdeal_eq (k + j)
    (Ideal.pow_le_pow_right (by omega) D.a₄_mem)
  have hprod := node_addX_product A W _ _ _ _ l v.nonsingular.1
    (by simpa only [he] using w.nonsingular.1) hxy hs
  have hx := node_addX_product_scaled A W D.uniformizer_ne_zero k j
    v.a w.a w.b l e₃ e₄ h3 h4 hprod
  have hline : (π ^ k * v.a - π ^ (k + j) * w.a) * l =
      π ^ k * v.b - π ^ (k + j) * w.b := by
    rw [pow_add]
    linear_combination π ^ k * hl
  obtain ⟨u', hu', _, _⟩ := exists_nodePointCoordinates_add_of_first_unit D v w
    hk hkw hw hb hd
  have hu : u.depth = j := (u.unique D.uniformizer_ne_zero D.maximalIdeal_eq u').1.trans hu'
  obtain ⟨hxu, hyu⟩ := node_addition_coordinate_values v w u l
    (by simpa only [he] using hxy) (by simpa only [he] using hs)
  have hf := node_difference_factor_residues W D.uniformizer_ne_zero hπ D.a₂_mem
    hl0 he₄ k j hk h3 hline hx
    (by simpa only [hu, he] using hxu.symm) (by simpa only [hu, he] using hyu.symm)
  exact ⟨hu, hf⟩

/-- The two original oriented characters obey a cleared quotient law. -/
theorem node_add_first_unit_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (P + Q))
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    residue A (v.b + W.a₁ * v.a) * residue A u.b =
      residue A W.a₁ ^ 3 * residue A w.b := by
  obtain ⟨_, hx, hy⟩ := node_add_first_unit_residues D v w u hk hkw hw hb hd
  have h := node_difference_vertical_character hx hy
  rw [map_add, map_mul, (residue_eq_zero_iff _).mpr hb, zero_add]
  linear_combination residue A W.a₁ * h

end FLT.Mazur
