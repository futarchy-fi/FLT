/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoefficients
public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# Actual transition maps between successive divided charts

Further division by t sends the old divided coordinates to t times the new
ones. These are actual chart morphisms, compatible with contraction to the
same original cubic. They need not be open immersions when t is not a unit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassDilatation

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t b3 b4 b6 c3 c4 c6 : R)
  (h3 : b3 = t * c3) (h4 : b4 = t * c4) (h6 : b6 = t ^ 2 * c6)

include h3 h4 h6 in
/-- Further scaling of the new coordinates solves the preceding divided equation. -/
theorem refinement_equation :
    let u := algebraMap R (Coordinate W (s * t) c3 c4 c6) t * x W (s * t) c3 c4 c6
    let v := algebraMap R (Coordinate W (s * t) c3 c4 c6) t * y W (s * t) c3 c4 c6
    v ^ 2 + (algebraMap R _ W.a₁ * u + algebraMap R _ b3) * v =
      algebraMap R _ s * u ^ 3 + algebraMap R _ W.a₂ * u ^ 2 +
        algebraMap R _ b4 * u + algebraMap R _ b6 := by
  dsimp only
  have h := equation W (s * t) c3 c4 c6
  simp only [map_mul] at h
  simp only [h3, h4, h6, map_mul, map_pow]
  linear_combination (algebraMap R (Coordinate W (s * t) c3 c4 c6) t) ^ 2 * h

/-- The actual coordinate map for further division by t. -/
def refinement : Coordinate W s b3 b4 b6 →ₐ[R] Coordinate W (s * t) c3 c4 c6 :=
  evaluation W s b3 b4 b6
    (algebraMap R _ t * x W (s * t) c3 c4 c6)
    (algebraMap R _ t * y W (s * t) c3 c4 c6)
    (refinement_equation W s t b3 b4 b6 c3 c4 c6 h3 h4 h6)

/-- The first old coordinate is t times the first new coordinate. -/
@[simp] theorem refinement_x :
    refinement W s t b3 b4 b6 c3 c4 c6 h3 h4 h6 (x W s b3 b4 b6) =
      algebraMap R _ t * x W (s * t) c3 c4 c6 := evaluation_x _ _ _ _ _ _ _ _

/-- The second old coordinate is t times the second new coordinate. -/
@[simp] theorem refinement_y :
    refinement W s t b3 b4 b6 c3 c4 c6 h3 h4 h6 (y W s b3 b4 b6) =
      algebraMap R _ t * y W (s * t) c3 c4 c6 := evaluation_y _ _ _ _ _ _ _ _

/-- Successive divisions preserve the actual original affine coordinates. -/
theorem refinement_fromOriginal
    (H3 : W.a₃ = s * b3) (H4 : W.a₄ = s * b4) (H6 : W.a₆ = s ^ 2 * b6)
    (H3' : W.a₃ = (s * t) * c3) (H4' : W.a₄ = (s * t) * c4)
    (H6' : W.a₆ = (s * t) ^ 2 * c6) :
    (refinement W s t b3 b4 b6 c3 c4 c6 h3 h4 h6).comp
        (fromOriginal W s b3 b4 b6 H3 H4 H6) =
      fromOriginal W (s * t) c3 c4 c6 H3' H4' H6' := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i <;>
    simp [WeierstrassIntegralChart.coord_self, mul_assoc]

end FLT.Mazur.WeierstrassDilatation
