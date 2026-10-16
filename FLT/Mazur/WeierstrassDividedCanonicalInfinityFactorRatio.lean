/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFullInfinityFactorRatioNaturality
public import FLT.Mazur.WeierstrassDividedCanonicalFactorRatioNaturality

/-!
# Canonical full infinity maps and their coefficient square

Each ring supplies its own canonical polynomial root. Root uniqueness identifies
the complete transported root before the regular infinity comparison is applied.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (h3a : W.a₃ ∈ I) (h4a : W.a₄ ∈ I) (h6a : W.a₆ ∈ I)
  [Fact (IsNilpotent (initialTangentSmoothing W ha s))] (k : ℕ)
local notation "r" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6

/-- The complete regular infinity chart with its independently constructed canonical root. -/
def canonicalFactorRatioInfinityPolygonMap :
    Spec (.of (WeierstrassIntegralChart.Coordinate W 1)) ⟶
      PolygonInfinitesimal.scheme R (initialTangentSmoothing W ha s) (2 * k + 3) (by omega) :=
  fullFactorRatioInfinityPolygonMap W s (initialTangentSmoothing W ha s) k
    b3 r I hI hm h3 h2 h3a h4a h6a

variable {S : Type u} [CommRing S] (f : R →+* S) (J : Ideal S)
  (hf : I ≤ J.comap f) (hJ : IsNilpotent J)
  [Fact (IsNilpotent (initialTangentSmoothing (W.map f) (ha.map f) (f s)))]
attribute [local irreducible] polynomialSlopeRoot fullFactorRatioInfinityPolygonMap

/-- Independently chosen canonical roots preserve the whole original infinity square. -/
@[reassoc] theorem canonicalFactorRatioInfinityPolygonMap_coefficient :
    canonicalFactorRatioInfinityPolygonMap (W.map f) (ha.map f)
      (f s) (f b3) (f b4) (f b6) J hJ (hf h2) (hf h3) (hf h4) (hf h6)
      (hf h3a) (hf h4a) (hf h6a) k ≫
        PolygonInfinitesimal.parameterProjection f (initialTangentSmoothing W ha s)
          (initialTangentSmoothing (W.map f) (ha.map f) (f s))
          (initialTangentSmoothing_map W ha s f) (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom (chartCoefficientRingMap f W 1)) ≫
        canonicalFactorRatioInfinityPolygonMap W ha s b3 b4 b6 I hI
          h2 h3 h4 h6 h3a h4a h6a k := by
  have he : Polynomial.map f r = polynomialSlopeRoot (W.map f) (f b3) (f b4) (f b6)
      J hJ (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6) :=
    polynomialSlopeRoot_coefficient f W b3 b4 b6 I J hf hI hJ ha h2 h3 h4 h6
  unfold canonicalFactorRatioInfinityPolygonMap
  simpa only [he] using fullFactorRatioInfinityPolygonMap_coefficient f W s
    (initialTangentSmoothing W ha s) (initialTangentSmoothing (W.map f) (ha.map f) (f s))
    (initialTangentSmoothing_map W ha s f) k b3 r I J hf hI hJ hm h3 h2 h3a h4a h6a

end FLT.Mazur.WeierstrassDividedDepth
