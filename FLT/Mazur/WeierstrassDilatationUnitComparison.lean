/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# The divided chart recovers the original affine chart when the scale is invertible

The inverse divides both actual original coordinates by the scaling unit.
Both composites are proved on the coordinate algebras. This is the local
isomorphism needed away from the exceptional fiber of a nodal modification.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : Rˣ) (b3 b4 b6 : R)
  (h3 : W.a₃ = ↑s * b3) (h4 : W.a₄ = ↑s * b4) (h6 : W.a₆ = (↑s : R) ^ 2 * b6)

/-- Multiplication by the scale reverses division in every coefficient algebra. -/
theorem scale_unscale {S : Type u} [CommRing S] [Algebra R S] (z : S) :
    algebraMap R S (↑s) * (algebraMap R S (↑s⁻¹) * z) = z := by
  rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

/-- Division reverses multiplication by the scale in every coefficient algebra. -/
theorem unscale_scale {S : Type u} [CommRing S] [Algebra R S] (z : S) :
    algebraMap R S (↑s⁻¹) * (algebraMap R S (↑s) * z) = z := by
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

include h3 h4 h6 in
/-- The divided original coordinates satisfy the new equation. -/
theorem unscaled_original_equation :
    let C := WeierstrassIntegralChart.Coordinate W 2
    let u := algebraMap R C (↑s⁻¹) * WeierstrassIntegralChart.coord W 2 0
    let v := algebraMap R C (↑s⁻¹) * WeierstrassIntegralChart.coord W 2 1
    v ^ 2 + (algebraMap R C W.a₁ * u + algebraMap R C b3) * v =
      algebraMap R C (↑s) * u ^ 3 + algebraMap R C W.a₂ * u ^ 2 +
        algebraMap R C b4 * u + algebraMap R C b6 := by
  apply equation_of_scaled W (↑s) b3 b4 b6 h3 h4 h6
    (s.isUnit.map (algebraMap R _)).isRegular
  simp only [scale_unscale]
  convert WeierstrassIntegralChart.coord_equation W 2 using 1
  ext i
  fin_cases i <;> simp [WeierstrassIntegralChart.coord_self]

/-- Explicit inverse algebra map, dividing the actual original coordinates by the scale. -/
def toOriginal : Coordinate W (↑s) b3 b4 b6 →ₐ[R]
    WeierstrassIntegralChart.Coordinate W 2 :=
  evaluation W (↑s) b3 b4 b6
    (algebraMap R _ (↑s⁻¹) * WeierstrassIntegralChart.coord W 2 0)
    (algebraMap R _ (↑s⁻¹) * WeierstrassIntegralChart.coord W 2 1)
    (unscaled_original_equation W s b3 b4 b6 h3 h4 h6)

/-- The divided-chart composite fixes its two actual coordinates. -/
theorem fromOriginal_comp_toOriginal :
    (fromOriginal W (↑s) b3 b4 b6 h3 h4 h6).comp
      (toOriginal W s b3 b4 b6 h3 h4 h6) = AlgHom.id R _ := by
  apply hom_ext
  · simp [toOriginal, unscale_scale]
  · simp [toOriginal, unscale_scale]

/-- The original-chart composite fixes all three normalized coordinates. -/
theorem toOriginal_comp_fromOriginal :
    (toOriginal W s b3 b4 b6 h3 h4 h6).comp
      (fromOriginal W (↑s) b3 b4 b6 h3 h4 h6) = AlgHom.id R _ := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i <;>
    simp [fromOriginal, toOriginal, WeierstrassIntegralChart.evaluation_coord,
      WeierstrassIntegralChart.coord_self, scale_unscale]

/-- Inverting the scale recovers precisely the original affine coordinate algebra. -/
def originalEquiv : WeierstrassIntegralChart.Coordinate W 2 ≃ₐ[R]
    Coordinate W (↑s) b3 b4 b6 :=
  AlgEquiv.ofAlgHom (fromOriginal W (↑s) b3 b4 b6 h3 h4 h6)
    (toOriginal W s b3 b4 b6 h3 h4 h6)
    (fromOriginal_comp_toOriginal W s b3 b4 b6 h3 h4 h6)
    (toOriginal_comp_fromOriginal W s b3 b4 b6 h3 h4 h6)

/-- The actual chart morphism to the cubic is an open immersion away from the scale. -/
theorem toCurve_isOpenImmersion_of_unit :
    IsOpenImmersion (toCurve W (↑s) b3 b4 b6 h3 h4 h6) := by
  let e := (originalEquiv W s b3 b4 b6 h3 h4 h6).toRingEquiv.toCommRingCatIso
  let _ : IsIso (Spec.map (CommRingCat.ofHom
      (fromOriginal W (↑s) b3 b4 b6 h3 h4 h6).toRingHom)) :=
    (Scheme.Spec.mapIso e.op).isIso_hom
  exact inferInstanceAs (IsOpenImmersion (Spec.map _ ≫
    WeierstrassIntegralChart.integralCurveChart W 2))

end FLT.Mazur.WeierstrassDilatation
