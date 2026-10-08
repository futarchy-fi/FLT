/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXAlgebra
public import FLT.Mazur.WeierstrassProjectivePointNaturality

/-!
# Contraction of the x-direction modification chart

The incidence and slope coordinates give an actual morphism to the same
original Weierstrass cubic. The original scale becomes t*x, and the original
vertical coordinate is x*v. No regularity or inversion hypothesis is needed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6 in
/-- The recovered original coordinates satisfy the original cubic equation. -/
theorem original_equation :
    (W.map (algebraMap R (Coordinate W s b3 b4 b6))).toProjective.Equation
      ![x W s b3 b4 b6, y W s b3 b4 b6, 1] := by
  rw [Projective.equation_iff]
  simp only [Projective.fin3_def_ext, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    h3, h4, h6, map_mul, map_pow, mul_one, one_pow]
  rw [← incidence W s b3 b4 b6]
  dsimp only [y, x]
  ring

/-- The actual coordinate map from the original affine cubic chart. -/
def fromOriginal : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] Coordinate W s b3 b4 b6 :=
  WeierstrassIntegralChart.evaluation W 2 ![x W s b3 b4 b6, y W s b3 b4 b6, 1]
    (original_equation W s b3 b4 b6 h3 h4 h6) rfl

/-- The horizontal original coordinate is the polynomial recovered from the divided equation. -/
@[simp] theorem fromOriginal_x :
    fromOriginal W s b3 b4 b6 h3 h4 h6 (WeierstrassIntegralChart.coord W 2 0) =
      x W s b3 b4 b6 := WeierstrassIntegralChart.evaluation_coord _ _ _ _ _ _

/-- The vertical original coordinate is the original horizontal coordinate times the slope. -/
@[simp] theorem fromOriginal_y :
    fromOriginal W s b3 b4 b6 h3 h4 h6 (WeierstrassIntegralChart.coord W 2 1) =
      y W s b3 b4 b6 := WeierstrassIntegralChart.evaluation_coord _ _ _ _ _ _

/-- The actual x-direction chart contracts to the original projective cubic. -/
def toCurve : Spec (.of (Coordinate W s b3 b4 b6)) ⟶
    WeierstrassIntegralChart.integralCurve W :=
  Spec.map (CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom) ≫
    WeierstrassIntegralChart.integralCurveChart W 2

/-- The contraction is a morphism over the original coefficient ring. -/
@[reassoc] theorem toCurve_structure :
    toCurve W s b3 b4 b6 h3 h4 h6 ≫ WeierstrassIntegralChart.integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s b3 b4 b6))) :=
  WeierstrassIntegralChart.integralChartPoint_structure W 2 _ _ _

/-- Every chart-valued point keeps the original incidence relation under contraction. -/
theorem mapped_incidence {S : Type u} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) :
    f (t W s b3 b4 b6) *
        f (fromOriginal W s b3 b4 b6 h3 h4 h6 (WeierstrassIntegralChart.coord W 2 0)) =
      algebraMap R S s := by
  simpa only [fromOriginal_x, map_mul, AlgHom.commutes] using
    congrArg f (incidence W s b3 b4 b6)

end FLT.Mazur.WeierstrassModificationX
