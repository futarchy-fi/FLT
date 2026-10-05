/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeBranchLabel
public import FLT.Mazur.EllipticNodePointBranches
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-!
# Negation exchanges the strict nodal branches

The actual inverse coordinate is -y-a₁x-a₃. Dividing by πᵏ changes the
second primitive coordinate to -b-a₁a-a₃/πᵏ. The last term vanishes in the
residue field, so inversion exchanges the two strict tangent branches.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  (W : WeierstrassCurve R)

omit [IsDomain R] [IsLocalRing R] in
/-- The inverse formula retains the same common coordinate factor. -/
theorem node_negY_scaled (π : R) (k : ℕ) (a b c : R) (h3 : W.a₃ = π ^ k * c) :
    W.toAffine.negY (π ^ k * a) (π ^ k * b) = π ^ k * (-b - W.a₁ * a - c) := by
  simp only [Affine.negY, h3]
  ring

omit [IsDomain R] in
/-- Negating a primitive pair preserves primitivity when the scaled a₃ vanishes. -/
theorem node_neg_primitive {a b c : R} (hc : c ∈ maximalIdeal R)
    (hp : IsUnit a ∨ IsUnit b) : IsUnit a ∨ IsUnit (-b - W.a₁ * a - c) := by
  by_cases ha : IsUnit a
  · exact Or.inl ha
  · right
    have hb := hp.resolve_left ha
    apply (residue_ne_zero_iff_isUnit _).mp
    have ha0 := (residue_eq_zero_iff _).mpr ha
    have hc0 := (residue_eq_zero_iff _).mpr hc
    simpa [ha0, hc0] using neg_ne_zero.mpr ((residue_ne_zero_iff_isUnit _).mpr hb)

omit [IsDomain R] in
/-- In the residue field the inverse's second factor is the negative first factor. -/
theorem node_neg_branch_mem_iff {a b c : R} (hc : c ∈ maximalIdeal R) :
    -b - W.a₁ * a - c ∈ maximalIdeal R ↔ b + W.a₁ * a ∈ maximalIdeal R := by
  rw [← residue_eq_zero_iff, ← residue_eq_zero_iff]
  have hc0 := (residue_eq_zero_iff _).mpr hc
  simp only [map_sub, map_neg, map_mul, hc0, sub_zero, map_add]
  rw [sub_eq_add_neg, ← neg_add, neg_eq_zero]

/-- The primitive-coordinate label changes sign under the actual inverse formula. -/
theorem nodeBranchLabel_neg (π : R) (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π}) (n k : ℕ) (hkn : k ≤ n / 2)
    (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ maximalIdeal R)
    (h3 : W.a₃ ∈ maximalIdeal R ^ (n + 1)) (h4 : W.a₄ ∈ maximalIdeal R ^ (n + 1))
    (h6 : W.a₆ ∈ maximalIdeal R ^ n) (a b c : R) (hc : c ∈ maximalIdeal R)
    (hp : IsUnit a ∨ IsUnit b)
    (he : W.toAffine.Equation (π ^ k * a) (π ^ k * b)) :
    nodeBranchLabel n k (-b - W.a₁ * a - c) = -nodeBranchLabel n k b := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hmid : 2 * k = n
  · rw [(nodeBranchLabel_middle hmid _).1, (nodeBranchLabel_middle hmid _).1]
    exact (nodeBranchLabel_middle hmid b).2
  have hb := (node_point_branches_below_middle W hπ hgen n k (by omega) (by omega)
    h1 h2 h3 h4 h6 a b hp he).2
  rcases hb with ⟨hb, hz⟩ | ⟨hb, hz⟩
  · rw [nodeBranchLabel_of_mem n k hb]
    apply nodeBranchLabel_of_unit hmid
    by_contra h
    exact (node_neg_branch_mem_iff W hc).mp h hz
  · rw [nodeBranchLabel_of_unit hmid hb, neg_neg]
    exact nodeBranchLabel_of_mem n k ((node_neg_branch_mem_iff W hc).mpr hz)

end FLT.Mazur
