/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticDilatationPointSection
public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# Every original singular-reduction point lifts to a bounded divided chart

The split nodal coefficient depth supplies all required divided coefficients.
The existing primitive coordinate theorem then produces an actual integral
section, at positive depth at most half the discriminant depth, whose
contraction is the canonical integral section of the original point.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)

include D in
/-- The actual split-depth hypotheses supply divided coefficients at every bounded depth. -/
theorem splitDepth_divided_coefficients (k : ℕ) (hk : 2 * k ≤ n) :
    ∃ b3 b4 b6 : R, W.a₃ = π ^ k * b3 ∧ W.a₄ = π ^ k * b4 ∧
      W.a₆ = (π ^ k) ^ 2 * b6 := by
  have h3 : W.a₃ ∈ maximalIdeal R ^ k := Ideal.pow_le_pow_right (by omega) D.a₃_mem
  have h4 : W.a₄ ∈ maximalIdeal R ^ k := Ideal.pow_le_pow_right (by omega) D.a₄_mem
  have h6 : W.a₆ ∈ maximalIdeal R ^ (2 * k) := Ideal.pow_le_pow_right hk D.a₆_mem
  rw [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3 h4 h6
  obtain ⟨b3, h3⟩ := h3
  obtain ⟨b4, h4⟩ := h4
  obtain ⟨b6, h6⟩ := h6
  refine ⟨b3, b4, b6, h3, h4, ?_⟩
  simpa only [← pow_mul, Nat.mul_comm k 2] using h6

variable {K : Type u} [Field K] (A : ValuationSubring K) (V : WeierstrassCurve A)
  {ϖ : A} {d : ℕ} (E : SplitNodeDepth V ϖ d)

include E in
/-- Every original point outside E₀ extends to an actual bounded divided affine chart. -/
theorem exists_splitNode_dilatation_section
    (P : (V.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A V P) :
    ∃ (k : ℕ) (_ : 0 < k) (_ : 2 * k ≤ d) (b3 b4 b6 : A)
      (h3 : V.a₃ = ϖ ^ k * b3) (h4 : V.a₄ = ϖ ^ k * b4)
      (h6 : V.a₆ = (ϖ ^ k) ^ 2 * b6)
      (q : Spec (.of A) ⟶ Spec (.of (Coordinate V (ϖ ^ k) b3 b4 b6))),
      q ≫ Spec.map (CommRingCat.ofHom
          (algebraMap A (Coordinate V (ϖ ^ k) b3 b4 b6))) = 𝟙 _ ∧
        q ≫ toCurve V (ϖ ^ k) b3 b4 b6 h3 h4 h6 =
          WeierstrassIntegralChart.integralPointSection A V P := by
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A V ϖ E.maximalIdeal_eq d
    E.a₃_mem E.a₄_mem E.a₆_not_mem P hP
  have hk : 2 * v.depth ≤ d := by omega
  have hk0 : 0 < v.depth := by
    have h0 : v.depth ≠ 0 := by
      intro he
      apply hP
      exact (v.smooth_iff
        (E.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)
        (Ideal.pow_le_self (by omega) E.a₃_mem)
        (Ideal.pow_le_self (by omega) E.a₄_mem)
        (Ideal.pow_le_self (Nat.ne_of_gt E.depth_pos) E.a₆_mem)).mpr he
    omega
  obtain ⟨b3, b4, b6, h3, h4, h6⟩ := splitDepth_divided_coefficients E v.depth hk
  exact ⟨v.depth, hk0, hk, b3, b4, b6, h3, h4, h6,
    nodePointSection A V E.uniformizer_ne_zero v b3 b4 b6 h3 h4 h6,
    nodePointSection_structure A V E.uniformizer_ne_zero v b3 b4 b6 h3 h4 h6,
    nodePointSection_toCurve A V E.uniformizer_ne_zero v b3 b4 b6 h3 h4 h6⟩

end FLT.Mazur.WeierstrassDilatation
