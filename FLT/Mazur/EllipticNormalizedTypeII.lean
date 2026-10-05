/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticComponentQuotient
public import FLT.Mazur.EllipticNormalizedSingularity
public import FLT.Mazur.EllipticSingularDivisibility

/-!
# The normalized type II component calculation

Suppose a₃,a₄,a₆ lie in the maximal ideal and a₆ is not in its square.
The only singular residual affine point is the origin, and the integral
equation excludes any generic point reducing to it. Thus E₀=E and E/E₀
is trivial. This proves the point-group calculation from coefficient tests;
it does not establish normal-form existence or Tate-algorithm exhaustiveness.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (h₃ : W.a₃ ∈ maximalIdeal A) (h₄ : W.a₄ ∈ maximalIdeal A)
  (h₆ : W.a₆ ∈ maximalIdeal A) (h₆₂ : W.a₆ ∉ maximalIdeal A ^ 2)

include h₃ h₄ h₆ h₆₂

/-- Every integral affine point has nonsingular reduction under the type II coefficient tests. -/
theorem normalizedTypeII_affine_nonsingular {x y : A} (h : W.toAffine.Equation x y) :
    (W.map (residue A)).toAffine.Nonsingular (residue A x) (residue A y) := by
  apply (normalized_nonsingular_iff (W.map (residue A))
    (by simpa using (residue_eq_zero_iff _).mpr h₃)
    (by simpa using (residue_eq_zero_iff _).mpr h₄)
    (by simpa using (residue_eq_zero_iff _).mpr h₆) (h.map (residue A))).mpr
  exact residue_pair_ne_zero_of_a₆_not_mem_sq W h h₃ h₄ h₆₂

/-- Every generic point reduces smoothly under the normalized type II tests. -/
theorem smoothReduction_of_normalizedTypeII
    (P : (W.map (algebraMap A K)).toProjective.Point) : SmoothReduction A W P := by
  classical
  have hall (Q : (W.map (algebraMap A K)).toAffine.Point) :
      SmoothReduction A W Q.toProjective := by
    cases Q with
    | zero => exact smoothReduction_zero A W
    | some x y hn =>
      by_cases hx : x ∈ A
      · have hy := W.mem_y_of_mem_x A hn.1 hx
        let x' : A := ⟨x, hx⟩
        let y' : A := ⟨y, hy⟩
        apply (smoothReduction_affine_iff A W x' y' hn).mpr
        apply normalizedTypeII_affine_nonsingular A W h₃ h₄ h₆ h₆₂
        exact (W.toAffine.map_equation (IsFractionRing.injective A K) x' y').mp hn.1
      · exact smoothReduction_of_nonintegral A W hn (fun h => hx h.1)
  have h := hall ((Point.toAffineAddEquiv _ ) P)
  change SmoothReduction A W
    ((Point.toAffineAddEquiv _).symm ((Point.toAffineAddEquiv _) P)) at h
  simpa only [AddEquiv.symm_apply_apply] using h

/-- In the normalized type II branch E₀ is the entire generic point group. -/
theorem ellipticE0_eq_top_of_normalizedTypeII : ellipticE0 A W = ⊤ := by
  apply top_unique
  intro P _
  exact smoothReduction_of_normalizedTypeII A W h₃ h₄ h₆ h₆₂ P

/-- The normalized type II rational component quotient is trivial. -/
theorem ellipticComponent_subsingleton_of_normalizedTypeII :
    Subsingleton (EllipticComponentQuotient A W) := by
  have hz (c : EllipticComponentQuotient A W) : c = 0 := by
    obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
    exact (ellipticComponentHom_eq_zero A W P).mpr
      (smoothReduction_of_normalizedTypeII A W h₃ h₄ h₆ h₆₂ P)
  exact ⟨fun c d => (hz c).trans (hz d).symm⟩

end FLT.Mazur
