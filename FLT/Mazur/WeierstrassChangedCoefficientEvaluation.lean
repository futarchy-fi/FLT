/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChartCoefficientRingMap
public import FLT.Mazur.WeierstrassAffineVariableChangeEquiv

/-!
# Evaluation after coefficient extension and full variable change

Scalar values and the two affine coordinate formulas identify the complete
composite ring map over an arbitrary coefficient homomorphism.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] affineVariableChangeMap chartCoefficientRingMap
variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  (f : R →+* S) (W : WeierstrassCurve R) (V : WeierstrassCurve S)
  (C : VariableChange S) (hC : C • W.map f = V)
  (φ : S →+* A) (p : Coordinate V 2 →+* A) (q : Coordinate W 2 →+* A)

/-- Full coefficient and variable substitution is detected by its original scalar and x,y values. -/
theorem changedCoefficientEvaluation_eq
    (hp : ∀ r, p (algebraMap S _ r) = φ r)
    (hq : ∀ r, q (algebraMap R _ r) = φ (f r))
    (hx : φ (C.u : S) ^ 2 * p (coord V 2 0) + φ C.r = q (coord W 2 0))
    (hy : φ (C.u : S) ^ 3 * p (coord V 2 1) +
      φ (C.u : S) ^ 2 * φ C.s * p (coord V 2 0) + φ C.t = q (coord W 2 1)) :
    p.comp ((affineVariableChangeMap (W.map f) V C hC).toRingHom.comp
      (chartCoefficientRingMap f W 2)) = q := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change p (affineVariableChangeMap _ _ _ _
      (chartCoefficientRingMap f W 2 (algebraMap R _ r))) = q (algebraMap R _ r)
    rw [chartCoefficientRingMap_scalar, AlgHom.commutes, hp, hq]
  · intro i
    change p (affineVariableChangeMap _ _ _ _
      (chartCoefficientRingMap f W 2 (coord W 2 i))) = q (coord W 2 i)
    rw [chartCoefficientRingMap_coord]
    fin_cases i
    · change p (affineVariableChangeMap _ _ _ _ (coord (W.map f) 2 0)) =
        q (coord W 2 0)
      simpa only [affineVariableChangeMap_x, map_add, map_mul, map_pow, hp] using hx
    · change p (affineVariableChangeMap _ _ _ _ (coord (W.map f) 2 1)) =
        q (coord W 2 1)
      simpa only [affineVariableChangeMap_y, map_add, map_mul, map_pow, hp] using hy
    · change p (affineVariableChangeMap _ _ _ _ (coord (W.map f) 2 2)) =
        q (coord W 2 2)
      simp only [coord_self, map_one]

end FLT.Mazur.WeierstrassIntegralChart
