/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXCoefficients
public import FLT.Mazur.WeierstrassModificationXMorphism
public import FLT.Mazur.WeierstrassIntegralCoefficientMap

/-!
# Coefficient extension preserves the complete original contraction

The initial affine coordinate map commutes with the original cubic contraction,
including both projective coordinates and every divided coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "q" => algebraMap R S
local notation "h3S" => (by simpa only [WeierstrassCurve.map_a₃, map_mul] using congrArg q h3)
local notation "h4S" => (by simpa only [WeierstrassCurve.map_a₄, map_mul] using congrArg q h4)
local notation "h6S" => (by
  simpa only [WeierstrassCurve.map_a₆, map_mul, map_pow] using congrArg q h6)

/-- Every original affine cubic function commutes with the full initial coefficient map. -/
theorem coefficientMap_fromOriginal :
    (coefficientMap W s b3 b4 b6 S).comp (fromOriginal W s b3 b4 b6 h3 h4 h6) =
      ((fromOriginal (W.map q) (q s) (q b3) (q b4) (q b6) h3S h4S h6S).restrictScalars R).comp
        (WeierstrassIntegralChart.chartCoefficientMap W 2) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, AlgHom.comp_apply, AlgHom.restrictScalars_apply, fromOriginal_x,
      WeierstrassIntegralChart.chartCoefficientMap_coord, x, map_sub, map_add, map_mul,
      map_pow, AlgHom.commutes, coefficientMap_t, coefficientMap_v,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, ← IsScalarTower.algebraMap_apply R S]
  · simp only [Fin.mk_one, AlgHom.comp_apply, AlgHom.restrictScalars_apply, fromOriginal_y,
      WeierstrassIntegralChart.chartCoefficientMap_coord, y, x, map_sub, map_add, map_mul,
      map_pow, AlgHom.commutes, coefficientMap_t, coefficientMap_v,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, ← IsScalarTower.algebraMap_apply R S]
  · simp only [Fin.reduceFinMk, WeierstrassIntegralChart.coord_self, map_one]

/-- The full initial contraction is natural under arbitrary coefficient extension. -/
@[reassoc] theorem coefficientMap_toCurve :
    Spec.map (CommRingCat.ofHom (coefficientMap W s b3 b4 b6 S).toRingHom) ≫
      toCurve W s b3 b4 b6 h3 h4 h6 =
        toCurve (W.map q) (q s) (q b3) (q b4) (q b6) h3S h4S h6S ≫
          WeierstrassIntegralChart.integralCoefficientMorphism W := by
  unfold toCurve
  rw [Category.assoc, WeierstrassIntegralChart.integralCurveChart_coefficientMorphism,
    ← Category.assoc, ← Category.assoc,
    WeierstrassIntegralChart.chartCoefficientMorphism, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (coefficientMap_fromOriginal (S := S) W s b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
