/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityIncidenceCoefficient
public import FLT.Mazur.WeierstrassInfinityFactorRatioParameter
public import FLT.Mazur.WeierstrassModificationXPolynomialCoefficientNaturality

/-!
# The complete infinity factor ratio commutes with coefficient change

Both pole-cleared factors keep their full polynomial corrections. Their unit
ratio follows the original coefficient map on the entire infinity chart.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R)
local notation "g" => chartCoefficientRingMap f W 1

/-- Polynomial evaluation retains both the full coefficients and the chosen chart element. -/
theorem chartCoefficientRingMap_eval (r : R[X]) (z : Coordinate W 1) :
    g (r.eval₂ (algebraMap R _) z) =
      (r.map f).eval₂ (algebraMap S _) (g z) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext (chartCoefficientRingMap_scalar f W 1)

variable (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
  (s b3 : R) (r : R[X])

/-- The complete small numerator follows coefficient extension on the full infinity chart. -/
theorem infinitySmallFactor_coefficient :
    g (infinitySmallFactor W I hI h2 h3 h4 h6 s r) =
      infinitySmallFactor (W.map f) J hJ (hf h2) (hf h3) (hf h4) (hf h6) (f s) (r.map f) := by
  rw [infinitySmallFactor, infinitySmallFactor, map_sub, map_one, map_mul,
    chartCoefficientRingMap_coord, chartCoefficientRingMap_eval,
    chartCoefficientRingMap_incidence f W I hI h2 h3 h4 h6 J hf hJ]

/-- The complete opposite numerator retains its linear and polynomial corrections. -/
theorem infinityOppositeFactor_coefficient :
    g (infinityOppositeFactor W I hI h2 h3 h4 h6 s b3 r) =
      infinityOppositeFactor (W.map f) J hJ (hf h2) (hf h3) (hf h4) (hf h6)
        (f s) (f b3) (r.map f) := by
  simp only [infinityOppositeFactor, map_add, map_mul, map_one,
    chartCoefficientRingMap_coord, chartCoefficientRingMap_scalar, chartCoefficientRingMap_eval,
    chartCoefficientRingMap_incidence f W I hI h2 h3 h4 h6 J hf hJ, WeierstrassCurve.map_a₁]

variable (hrI : r ∈ I.map C) (hb3 : b3 ∈ I)
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI
local notation "a" => infinityFactorRatioUnit W I hI h2 h3 h4 h6 s b3 r hrI hb3
local notation "b" => infinityFactorRatioUnit (W.map f) J hJ
  (hf h2) (hf h3) (hf h4) (hf h6) (f s) (f b3) (r.map f) hrJ (hf hb3)

/-- The full regular infinity ratio is natural, including every nilpotent correction. -/
theorem infinityFactorRatioUnit_coefficient : Units.map (g).toMonoidHom a = b := by
  apply Units.ext
  change g (a : Coordinate W 1) = (b : Coordinate (W.map f) 1)
  apply (infinityOppositeFactor_isUnit (W.map f) J hJ (hf h2) (hf h3) (hf h4) (hf h6)
    (f s) (f b3) (r.map f) hrJ (hf hb3)).mul_right_cancel
  rw [← infinityOppositeFactor_coefficient f W I J hf hI hJ h2 h3 h4 h6 s b3 r,
    ← map_mul, infinityFactorRatioUnit_denominator,
    infinitySmallFactor_coefficient f W I J hf hI hJ h2 h3 h4 h6 s r,
    infinityOppositeFactor_coefficient f W I J hf hI hJ h2 h3 h4 h6 s b3 r,
    infinityFactorRatioUnit_denominator]

end FLT.Mazur.WeierstrassIntegralChart
