/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCanonicalFactorRatioAffine
public import FLT.Mazur.WeierstrassModificationXCanonicalFactorRatioTransport

/-!
# Canonical full affine coefficient squares

The independently constructed roots agree under coefficient restriction. The
whole glued affine comparison therefore follows the original coefficient map.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s b3 b4 b6 : R)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  [Fact (IsNilpotent (initialTangentSmoothing W ha s))]
  [Fact (IsNilpotent (initialTangentSmoothing (W.map f) (ha.map f) (f s)))] (k : ℕ)
local notation "r" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
attribute [local irreducible] polynomialSlopeRoot factorRatioInitialAffinePolygonMap

/-- The entire canonical affine map commutes with arbitrary compatible coefficient changes. -/
@[reassoc] theorem canonicalFactorRatioAffinePolygonMap_coefficient :
    canonicalFactorRatioAffinePolygonMap (W.map f) (ha.map f)
      (f s) (f b3) (f b4) (f b6) J hJ (hf h2) (hf h3) (hf h4) (hf h6) k ≫
        PolygonInfinitesimal.parameterProjection f (initialTangentSmoothing W ha s)
          (initialTangentSmoothing (W.map f) (ha.map f) (f s))
          (initialTangentSmoothing_map W ha s f) (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom (coefficientRingMap f W s b3 b4 b6)) ≫
        canonicalFactorRatioAffinePolygonMap W ha s b3 b4 b6 I hI h2 h3 h4 h6 k := by
  have he : Polynomial.map f r = polynomialSlopeRoot (W.map f) (f b3) (f b4) (f b6)
      J hJ (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6) :=
    polynomialSlopeRoot_coefficient f W b3 b4 b6 I J hf hI hJ ha h2 h3 h4 h6
  unfold canonicalFactorRatioAffinePolygonMap
  simpa only [he] using factorRatioInitialAffinePolygonMap_coefficient f W ha s
    (initialTangentSmoothing W ha s) (initialTangentSmoothing_factor W ha s)
    (initialTangentSmoothing (W.map f) (ha.map f) (f s))
    (initialTangentSmoothing_factor (W.map f) (ha.map f) (f s))
    (initialTangentSmoothing_map W ha s f) k b3 b4 b6 r hr I J hf hI hJ hm h3

end FLT.Mazur.WeierstrassDividedDepth
