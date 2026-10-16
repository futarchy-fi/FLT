/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioAffineNaturality
public import FLT.Mazur.WeierstrassDividedFactorRatioAffineInfinity
public import FLT.Mazur.WeierstrassModificationXCanonicalFactorRatioChart

/-!
# Canonical full initial affine comparisons

The full affine gluing uses the independently constructed polynomial root.
Both original node restrictions and the entire original infinity boundary survive.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s b3 b4 b6 : R) (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  [Fact (IsNilpotent (initialTangentSmoothing W ha s))] (k : ℕ)
local notation "r" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "τ" => initialTangentSmoothing W ha s
local notation "N" => polynomialNodeChart W s b3 b4 b6 r hr I hI hm h3
local notation "O" => polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hm h3

/-- The entire original affine scheme maps to the polygon using the canonical corrected root. -/
def canonicalFactorRatioAffinePolygonMap : Spec (.of (Coordinate W s b3 b4 b6)) ⟶
    PolygonInfinitesimal.scheme R τ (2 * k + 3) (by omega) :=
  factorRatioInitialAffinePolygonMap W ha s τ (initialTangentSmoothing_factor W ha s)
    k b3 b4 b6 r hr I hI hm h3
local notation "f" => canonicalFactorRatioAffinePolygonMap W ha s b3 b4 b6 I hI h2 h3 h4 h6 k

/-- Both canonical node opens have their full corrected charts at the original cyclic labels. -/
@[reassoc] theorem canonicalFactorRatioAffinePolygonMap_chart (b : Bool) :
    (if b then O else N) ≫ f =
      canonicalFactorRatioChart W ha s b3 b4 b6 I hI h2 h3 h4 h6 ≫
        (if b then (branchSwapIso R τ).hom else 𝟙 _) ≫
          PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega) (initialPolygonIndex k b) :=
  factorRatioInitialAffinePolygonMap_chart ..

/-- The canonical full affine comparison preserves the original coefficient structure. -/
@[reassoc] theorem canonicalFactorRatioAffinePolygonMap_structure :
    f ≫ PolygonInfinitesimal.toBase R τ (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s b3 b4 b6))) :=
  factorRatioInitialAffinePolygonMap_structure ..

/-- The canonical map retains the full original D(y) parameter, with all nilpotent corrections. -/
@[reassoc] theorem canonicalFactorRatioAffinePolygonMap_infinity_boundary :
    polynomialInitialInfinityInclusion W s b3 b4 b6 ≫ f =
      factorRatioInfinityParameter W s b3 b4 b6 r hr I hI hm h3 ≫ rightBranchOpen R τ ≫
        PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega) (initialPolygonIndex k false) :=
  factorRatioInitialAffinePolygonMap_infinity_boundary ..

end FLT.Mazur.WeierstrassDividedDepth
