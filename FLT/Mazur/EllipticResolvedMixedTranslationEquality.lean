/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedLaurentEquality
public import FLT.Mazur.EllipticNodeMixedLaurentCharacter

/-!
# Translation equality outside E₀ in the actual resolved smooth fiber

Fix a deeper point with unit vertical parameter, including a midpoint point.
Translation by it preserves and reflects specialization equality between two
shallower first-branch points at the same depth. The outputs lie on the negative
branch at the depth difference; their coordinates are constructed from actual addition.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open IsLocalRing
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P P' Q : (W.map (algebraMap A K)).toProjective.Point}

/-- A deeper opposite-branch translation preserves and detects actual smooth-fiber equality. -/
theorem resolvedSplitSmoothPoint_mixed_translation_eq_iff
    (v : NodePointCoordinates A W π P) (v' : NodePointCoordinates A W π P')
    (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (he : v'.depth = v.depth)
    (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : v.b ∈ maximalIdeal A) (hb' : v'.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    resolvedSplitSmoothPoint A D (P + Q) = resolvedSplitSmoothPoint A D (P' + Q) ↔
      resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D P' := by
  obtain ⟨t, ht, _, htb⟩ := exists_nodePointCoordinates_add_of_first_unit D v w hk hkw hw hb hd
  obtain ⟨t', ht', _, ht'b⟩ := exists_nodePointCoordinates_add_of_first_unit D v' w
    (by omega) (by omega) hw hb' hd
  rw [resolvedSplitSmoothPoint_negative_eq_iff A D (w.depth - v.depth) (by omega)
    (by omega) (P + Q) (P' + Q) t ht t' (by omega) htb ht'b,
    resolvedSplitSmoothPoint_positive_eq_iff A D v.depth hk (by omega)
      P P' v rfl v' he hb hb']
  have h := node_add_first_unit_character D v w t hk hkw hw hb hd
  have h' := node_add_first_unit_character D v' w t' (by omega) (by omega) hw hb' hd
  have hc : residue A W.a₁ ^ 3 * residue A w.b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (D.a₁_unit.map (residue A)).ne_zero)
      (hd.map (residue A)).ne_zero
  have hs : residue A (v.b + W.a₁ * v.a) ≠ 0 := by
    intro hz
    apply hc
    rw [← h, hz, zero_mul]
  constructor
  · intro htchar
    apply mul_right_cancel₀ (htb.map (residue A)).ne_zero
    rw [h]
    simpa only [← htchar] using h'.symm
  · intro hchar
    apply mul_left_cancel₀ hs
    rw [h]
    simpa only [← hchar] using h'.symm

end FLT.Mazur.WeierstrassDividedDepth
