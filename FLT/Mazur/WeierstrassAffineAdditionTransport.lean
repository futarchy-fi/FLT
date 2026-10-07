/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProductOverlapScheme
public import FLT.Mazur.WeierstrassAdditionSchemeCover

/-!
# Transporting the four affine addition domains through input transitions

Pull back the existing affine addition cover along the normalized input map.
Each transported domain has an actual regular addition morphism to its output
chart, and the input squares commute as scheme morphisms.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The ordinary laws have affine output and the reciprocal laws have Y-chart output. -/
def additionChartOutput : AdditionChartIndex → Fin 3
  | .secant | .tangent => 2
  | .verticalSecant | .verticalTangent => 1

/-- Every member of the affine addition cover has its constructed output morphism. -/
def additionChartSpec (i : AdditionChartIndex) :
    Spec (additionChartRing W i) ⟶
      Spec (CommRingCat.of (Coordinate W (additionChartOutput i))) :=
  match i with
  | .secant => Spec.map (CommRingCat.ofHom (secantAddition W).toRingHom)
  | .tangent => Spec.map (CommRingCat.ofHom (tangentAddition W).toRingHom)
  | .verticalSecant => Spec.map (CommRingCat.ofHom (verticalSecantAddition W).toRingHom)
  | .verticalTangent => Spec.map (CommRingCat.ofHom (verticalTangentAddition W).toRingHom)

variable (j k : Fin 3)

/-- The input overlap maps openly to the affine input product by changing both charts. -/
def affineInputOverlapMap : Spec (CommRingCat.of (ProductOverlap W j k 2 2)) ⟶
    Spec (CommRingCat.of (AffineProduct W)) :=
  Spec.map (CommRingCat.ofHom (productOverlapOther W j k 2 2).toRingHom)

/-- Normalization of the two inputs is an actual open immersion. -/
instance affineInputOverlapMap_isOpenImmersion :
    IsOpenImmersion (affineInputOverlapMap W j k) :=
  productOverlapOther_isOpenImmersion W j k 2 2

/-- The four affine addition opens transported onto any affine input overlap. -/
def affineOverlapAdditionCover (hΔ : IsUnit W.Δ) :
    (Spec (CommRingCat.of (ProductOverlap W j k 2 2))).OpenCover :=
  (additionAffineOpenCover W hΔ).pullback₁ (affineInputOverlapMap W j k)

/-- The second projection retains the original affine addition domain. -/
def affineOverlapAdditionProjection (hΔ : IsUnit W.Δ) (i : AdditionChartIndex) :
    (affineOverlapAdditionCover W j k hΔ).X i ⟶ Spec (additionChartRing W i) :=
  (additionAffineOpenCover W hΔ).pullbackHom (affineInputOverlapMap W j k) i

/-- The transported addition domain has the same affine inputs along both routes. -/
@[reassoc] theorem affineOverlapAdditionProjection_inputs (hΔ : IsUnit W.Δ)
    (i : AdditionChartIndex) :
    affineOverlapAdditionProjection W j k hΔ i ≫ additionChartInclusion W i =
      (affineOverlapAdditionCover W j k hΔ).f i ≫ affineInputOverlapMap W j k :=
  Scheme.Cover.pullbackHom_map _ _ _

/-- Addition on each transported open is a regular morphism into its normalized chart. -/
def affineOverlapAdditionSpec (hΔ : IsUnit W.Δ) (i : AdditionChartIndex) :
    (affineOverlapAdditionCover W j k hΔ).X i ⟶
      Spec (CommRingCat.of (Coordinate W (additionChartOutput i))) :=
  affineOverlapAdditionProjection W j k hΔ i ≫ additionChartSpec W i

/-- Each transported domain remains open in the original projective input chart product. -/
instance affineOverlapAdditionInclusion_isOpenImmersion (hΔ : IsUnit W.Δ)
    (i : AdditionChartIndex) :
    IsOpenImmersion ((affineOverlapAdditionCover W j k hΔ).f i ≫
      Spec.map (CommRingCat.ofHom (productOverlapRestriction W j k 2 2).toRingHom)) := by
  have : IsOpenImmersion ((affineOverlapAdditionCover W j k hΔ).f i) :=
    (affineOverlapAdditionCover W j k hΔ).map_prop i
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
