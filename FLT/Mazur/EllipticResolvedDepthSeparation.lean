/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteEarlierNodeEquality

/-!
# Actual resolved points separate primitive depths

At the smaller depth, a deeper point has both divided residues zero.
A primitive point has a nonzero divided residue, so equality of actual
resolved specializations forces equal primitive depths and equal residues.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D in
/-- A positive extra depth kills every earlier divided coordinate in the residue field. -/
theorem earlierNode_residue_zero {k l : ℕ} (h : k < l) (x : A) :
    residue A (π ^ (l - k) * x) = 0 := by
  have hz : residue A π = 0 := (residue_eq_zero_iff _).mpr
    (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  rw [map_mul, map_pow, hz,
    zero_pow (by omega : l - k ≠ 0), zero_mul]

/-- Actual resolved equality prevents one bounded primitive depth from being smaller. -/
theorem resolvedSplitSmoothPoint_depth_not_lt
    (v : NodePointCoordinates A W π P) (hv : v.depth ≤ n / 2)
    (w : NodePointCoordinates A W π Q)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    ¬ v.depth < w.depth := by
  intro h
  obtain ⟨ha, hb⟩ := resolvedSplitSmoothPoint_earlier_residues A P Q D v.depth hv
    v (le_refl _) w (Nat.le_of_lt h) he
  simp only [Nat.sub_self, pow_zero, one_mul] at ha hb
  rw [earlierNode_residue_zero A D h] at ha hb
  rcases v.primitive with hu | hu
  · exact ((residue_ne_zero_iff_isUnit _).mpr hu) ha
  · exact ((residue_ne_zero_iff_isUnit _).mpr hu) hb

/-- Equal actual resolved points have the same bounded primitive depth. -/
theorem resolvedSplitSmoothPoint_depth_eq
    (v : NodePointCoordinates A W π P) (hv : v.depth ≤ n / 2)
    (w : NodePointCoordinates A W π Q) (hw : w.depth ≤ n / 2)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    v.depth = w.depth := by
  have h₁ := resolvedSplitSmoothPoint_depth_not_lt A D v hv w he
  have h₂ := resolvedSplitSmoothPoint_depth_not_lt A D w hw v he.symm
  omega

/-- Equal actual resolved points have the same primitive divided residues. -/
theorem resolvedSplitSmoothPoint_primitive_residues
    (v : NodePointCoordinates A W π P) (hv : v.depth ≤ n / 2)
    (w : NodePointCoordinates A W π Q) (hw : w.depth ≤ n / 2)
    (he : resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D Q) :
    residue A v.a = residue A w.a ∧ residue A v.b = residue A w.b := by
  have hd := resolvedSplitSmoothPoint_depth_eq A D v hv w hw he
  have hr := resolvedSplitSmoothPoint_earlier_residues A P Q D v.depth hv
    v (le_refl _) w (by omega) he
  simpa only [hd, Nat.sub_self, pow_zero, one_mul] using hr

end FLT.Mazur.WeierstrassDividedDepth
