/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioChartNaturality
public import FLT.Mazur.WeierstrassModificationXCanonicalNodeCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXInitialMobiusNormalization

/-!
# Canonical corrected polygon charts

The polynomial root is constructed separately in each nilpotent coefficient ideal.
Uniqueness carries the corrected full chart through the original coefficient map.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "r" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "τ" => initialTangentSmoothing W ha s

/-- The corrected full polygon chart with its constructed root and exact normalized smoothing. -/
def canonicalFactorRatioChart : Spec (.of (PolynomialNodeOpen W s)) ⟶
    PolygonSmoothing.chart R τ :=
  polynomialFactorRatioChart W ha s τ (initialTangentSmoothing_factor W ha s)
    b3 b4 b6 r hr I hI hm h3

instance canonicalFactorRatioChart_isOpenImmersion :
    IsOpenImmersion (canonicalFactorRatioChart W ha s b3 b4 b6 I hI h2 h3 h4 h6) :=
  polynomialFactorRatioChart_isOpenImmersion ..

/-- The canonical corrected polygon chart retains the complete original coefficient structure. -/
@[reassoc] theorem canonicalFactorRatioChart_structure :
    canonicalFactorRatioChart W ha s b3 b4 b6 I hI h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonSmoothing.ChartRing τ))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (PolynomialNodeOpen W s))) :=
  polynomialFactorRatioChart_structure ..

variable {S : Type u} [CommRing S] (f : R →+* S)
  (J : Ideal S) (hf : I ≤ J.comap f) (hJ : IsNilpotent J)
attribute [local irreducible] polynomialSlopeRoot polynomialFactorRatioChart

/-- Independent canonical roots give the exact corrected full coefficient square. -/
@[reassoc] theorem canonicalFactorRatioChart_coefficient :
    Spec.map (CommRingCat.ofHom (nodeOpenCoefficientRingMap f W s)) ≫
      canonicalFactorRatioChart W ha s b3 b4 b6 I hI h2 h3 h4 h6 =
        canonicalFactorRatioChart (W.map f) (ha.map f) (f s) (f b3) (f b4) (f b6)
          J hJ (hf h2) (hf h3) (hf h4) (hf h6) ≫
            Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap f τ
              (initialTangentSmoothing (W.map f) (ha.map f) (f s))
              (initialTangentSmoothing_map W ha s f))) := by
  have he : Polynomial.map f r = polynomialSlopeRoot (W.map f) (f b3) (f b4) (f b6)
      J hJ (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6) :=
    polynomialSlopeRoot_coefficient f W b3 b4 b6 I J hf hI hJ ha h2 h3 h4 h6
  unfold canonicalFactorRatioChart
  simpa only [he] using
    polynomialFactorRatioChart_coefficient f W ha s τ (initialTangentSmoothing_factor W ha s)
      (initialTangentSmoothing (W.map f) (ha.map f) (f s))
      (initialTangentSmoothing_factor (W.map f) (ha.map f) (f s))
      (initialTangentSmoothing_map W ha s f) b3 b4 b6 r hr I J hf hI hJ hm h3

end FLT.Mazur.WeierstrassModificationX
