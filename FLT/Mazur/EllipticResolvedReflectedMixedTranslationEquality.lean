/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentCharacterEquality
public import FLT.Mazur.EllipticNodeReflectedMixedCharacter

/-!
# Reflected mixed translation in the actual resolved fiber

A deeper point with unit positive tangent character translates the shallower
negative component to a positive component at the depth difference. The
original character formula preserves and reflects actual specialization equality.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open IsLocalRing
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P P' Q : (W.map (algebraMap A K)).toProjective.Point}

/-- A deeper opposite-branch translation preserves and detects actual smooth-fiber equality. -/
theorem resolvedSplitSmoothPoint_reflected_mixed_translation_eq_iff
    (v : NodePointCoordinates A W π P) (v' : NodePointCoordinates A W π P')
    (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (he : v'.depth = v.depth)
    (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : IsUnit v.b) (hb' : IsUnit v'.b) (hd : IsUnit (w.b + W.a₁ * w.a)) :
    resolvedSplitSmoothPoint A D (P + Q) = resolvedSplitSmoothPoint A D (P' + Q) ↔
      resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D P' := by
  obtain ⟨t, ht⟩ := exists_nodePointCoordinates_add_of_unit_tangent D v w hk hkw hw hb hd
  obtain ⟨t', ht'⟩ := exists_nodePointCoordinates_add_of_unit_tangent D v' w
    (by omega) (by omega) hw hb' hd
  have htb : t.b ∈ maximalIdeal A := (residue_eq_zero_iff _).mp
    (node_add_unit_tangent_residues D v w t hk hkw hw hb hd).2.2
  have ht'b : t'.b ∈ maximalIdeal A := (residue_eq_zero_iff _).mp
    (node_add_unit_tangent_residues D v' w t' (by omega) (by omega) hw hb' hd).2.2
  rw [resolvedSplitSmoothPoint_strict_positive_eq_iff A D (w.depth - v.depth) (by omega)
    (by omega) (P + Q) (P' + Q) t ht t' (by omega) htb ht'b,
    resolvedSplitSmoothPoint_strict_negative_eq_iff A D v.depth hk (by omega)
      P P' v rfl v' he hb hb']
  have h := node_add_unit_tangent_character D v w t hk hkw hw hb hd
  have h' := node_add_unit_tangent_character D v' w t' (by omega) (by omega) hw hb' hd
  have hc : -(residue A W.a₁ ^ 3 * residue A (w.b + W.a₁ * w.a)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (D.a₁_unit.map (residue A)).ne_zero)
      (hd.map (residue A)).ne_zero)
  have htunit : residue A (t.b + W.a₁ * t.a) ≠ 0 := by
    intro hz
    apply hc
    rw [← h, hz, mul_zero]
  constructor
  · intro htchar
    apply mul_right_cancel₀ htunit
    rw [h]
    simpa only [← htchar] using h'.symm
  · intro hchar
    apply mul_left_cancel₀ (hb.map (residue A)).ne_zero
    rw [h]
    simpa only [← hchar] using h'.symm

end FLT.Mazur.WeierstrassDividedDepth
