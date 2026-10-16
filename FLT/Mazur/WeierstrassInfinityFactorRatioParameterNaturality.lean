/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityFactorRatioCoefficient
public import FLT.Mazur.PolygonScalingNaturality

/-!
# The full infinity torus parameter follows coefficient restriction

The complete Laurent evaluation square follows from the exact unit identity.
It retains both inverse generators and all original coefficient scalars.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
  (s b3 : R) (r : R[X]) (hrI : r ∈ I.map C) (hb3 : b3 ∈ I)
local notation "g" => chartCoefficientRingMap f W 1
local notation "c" => PolygonScalingNaturality.coeffMap f
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI
local notation "a" => infinityFactorRatioUnit W I hI h2 h3 h4 h6 s b3 r hrI hb3
local notation "b" => infinityFactorRatioUnit (W.map f) J hJ
  (hf h2) (hf h3) (hf h4) (hf h6) (f s) (f b3) (r.map f) hrJ (hf hb3)

/-- The full Laurent evaluation follows the actual coefficient map on every function. -/
theorem infinityFactorRatioEvaluation_coefficient :
    (g).comp (LaurentUnitPoints.evalUnit a).toRingHom =
      (LaurentUnitPoints.evalUnit b).toRingHom.comp c := by
  have hu := infinityFactorRatioUnit_coefficient f W I J hf hI hJ h2 h3 h4 h6 s b3 r hrI hb3
  apply PolygonScalingNaturality.ringHom_ext
  · intro z
    change g (LaurentUnitPoints.evalUnit a (LaurentPolynomial.C z)) =
      LaurentUnitPoints.evalUnit b (c (LaurentPolynomial.C z))
    rw [LaurentUnitPoints.evalUnit_C, PolygonScalingNaturality.coeffMap_C,
      LaurentUnitPoints.evalUnit_C, chartCoefficientRingMap_scalar]
  · change g (LaurentUnitPoints.evalUnit a (LaurentPolynomial.T 1)) =
      LaurentUnitPoints.evalUnit b (c (LaurentPolynomial.T 1))
    simp only [LaurentUnitPoints.evalUnit_T, zpow_one,
      PolygonScalingNaturality.coeffMap_T_one]
    exact congrArg Units.val hu
  · change g (LaurentUnitPoints.evalUnit a (LaurentPolynomial.T (-1))) =
      LaurentUnitPoints.evalUnit b (c (LaurentPolynomial.T (-1)))
    simp only [LaurentUnitPoints.evalUnit_T, zpow_neg_one,
      PolygonScalingNaturality.coeffMap_T_neg_one]
    exact congrArg (fun z : (Coordinate (W.map f) 1)ˣ => (↑z⁻¹ : Coordinate (W.map f) 1)) hu

/-- The full original infinity parameter commutes with its complete coefficient square. -/
@[reassoc] theorem infinityFactorRatioParameter_coefficient :
    Spec.map (CommRingCat.ofHom g) ≫
      infinityFactorRatioParameter W I hI h2 h3 h4 h6 s b3 r hrI hb3 =
      infinityFactorRatioParameter (W.map f) J hJ
        (hf h2) (hf h3) (hf h4) (hf h6) (f s) (f b3) (r.map f) hrJ (hf hb3) ≫
          Spec.map (CommRingCat.ofHom c) := by
  unfold infinityFactorRatioParameter
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (infinityFactorRatioEvaluation_coefficient f W I J hf hI hJ h2 h3 h4 h6 s b3 r hrI hb3)

end FLT.Mazur.WeierstrassIntegralChart
