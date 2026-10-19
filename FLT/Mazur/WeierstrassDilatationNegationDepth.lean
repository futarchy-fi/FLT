/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationNegation
public import FLT.Mazur.WeierstrassDilatationDepthTransition

/-!
# Negation commutes with the actual divided-depth transitions

The quotient of the original third coefficient supplies the necessary vertical
correction. No independent compatibility hypothesis is imposed on depth data.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t b3 b4 b6 c3 c4 c6 : R)
  (h3 : b3 = t * c3) (h4 : b4 = t * c4) (h6 : b6 = t ^ 2 * c6)

/-- The integral negative commutes with every actual refinement of the divided chart. -/
theorem negation_refinement :
    (negation W (s * t) c3 c4 c6).comp
        (refinement W s t b3 b4 b6 c3 c4 c6 h3 h4 h6) =
      (refinement W s t b3 b4 b6 c3 c4 c6 h3 h4 h6).comp (negation W s b3 b4 b6) := by
  apply hom_ext
  · simp only [AlgHom.comp_apply, refinement_x, map_mul, AlgHom.commutes, negation_x]
  · simp only [AlgHom.comp_apply, refinement_y, negation_y, map_mul, map_sub,
      map_neg, AlgHom.commutes, refinement_x, h3]
    ring

variable [IsDomain R] (π : R) (k l : ℕ) (hπ : π ≠ 0) (hkl : k ≤ l)
  (H3 : W.a₃ = π ^ k * b3) (H4 : W.a₄ = π ^ k * b4)
  (H6 : W.a₆ = (π ^ k) ^ 2 * b6)
  (H3' : W.a₃ = π ^ l * c3) (H4' : W.a₄ = π ^ l * c4)
  (H6' : W.a₆ = (π ^ l) ^ 2 * c6)

/-- At arbitrary depths, the actual coefficient factorizations force inverse compatibility. -/
theorem negation_depthTransition :
    (negation W (π ^ l) c3 c4 c6).comp
        (depthTransition π k l hπ hkl W b3 b4 b6 c3 c4 c6 H3 H4 H6 H3' H4' H6') =
      (depthTransition π k l hπ hkl W b3 b4 b6 c3 c4 c6 H3 H4 H6 H3' H4' H6').comp
        (negation W (π ^ k) b3 b4 b6) := by
  apply hom_ext
  · simp only [AlgHom.comp_apply, depthTransition_x, map_mul, AlgHom.commutes, negation_x]
  · simp only [AlgHom.comp_apply, depthTransition_y, negation_y, map_mul, map_sub,
      map_neg, AlgHom.commutes, depthTransition_x]
    rw [depth_coefficient_factor π k l hπ hkl H3 H3', map_mul]
    ring

end FLT.Mazur.WeierstrassDilatation
