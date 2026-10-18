/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryTestCharts
public import FLT.Mazur.RelativeExactRankFactorization

/-!
# Actual rank-stage factorizations of boundary test neighborhoods

Each test-ideal neighborhood, pulled to the original chart, factors through
some finite matching rank stage as a scheme. This is stronger than pointwise
rank coverage and retains every nilpotent coefficient. No coverage of the full
scalar product is assumed or concluded.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct boundaryCoordinate
  rankPullbackThickening rankPullbackMap
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [TopologicalSpace.NoetherianSpace U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local instance testFactorOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance testFactorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance testFactorOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
variable (k : ℕ)


/-- The original test chart maps to the full chart boundary over the unchanged scalar product. -/
def boundaryTestChartMap :
    boundaryTestChart n o U e hU s κ k ⟶ chartBoundary n o U e hU s κ :=
  pullback.lift
    (pullback.fst (quotientMap ρ)
      (boundaryTestThickeningMap s κ tests k ≫ boundaryProjection s κ))
    (boundaryTestChartProjection n o U e hU s κ k ≫
      boundaryTestThickeningMap s κ tests k)
    (by rw [Category.assoc]; exact pullback.condition)

omit [QuasiCompact p] in
/-- The map preserves the actual relation endpoint, including its coefficient structure. -/
@[reassoc]
theorem boundaryTestChartMap_endpoint :
    boundaryTestChartMap n o U e hU s κ k ≫ b =
      boundaryTestChartEndpoint n o U e hU s κ k := by
  simp only [boundaryTestChartMap, chartBoundaryEndpoint, boundaryTestChartEndpoint,
    chartBoundaryChart, pullback.lift_fst_assoc]

omit [QuasiCompact p] in
/-- The same map preserves the full scalar boundary point and its original prime. -/
@[reassoc]
theorem boundaryTestChartMap_product :
    boundaryTestChartMap n o U e hU s κ k ≫ chartBoundaryProduct n o U e hU s κ =
      boundaryTestChartProjection n o U e hU s κ k ≫
        boundaryTestThickeningMap s κ tests k := by
  exact pullback.lift_snd _ _ _

attribute [local irreducible] boundaryTestChartMap chartBoundaryEndpoint
  boundaryTestChartEndpoint chartBoundary

variable [AlgebraicGeometry.IsNoetherian A]

/-- Every compact coefficient chart of a test neighborhood lifts to a finite matching rank stage. -/
theorem exists_boundaryTestChart_rank_factor {Y : Scheme.{0}} [CompactSpace Y]
    (v : Y ⟶ boundaryTestChart n o U e hU s κ k) :
    ∃ (l : ℕ) (w : Y ⟶ rankPullbackThickening (Over.mk p) b n l),
      w ≫ rankPullbackMap (Over.mk p) b n l =
        v ≫ boundaryTestChartMap n o U e hU s κ k := by
  apply exists_rankPullback_factor
  rw [Category.assoc, boundaryTestChartMap_endpoint]
  rintro _ ⟨y, rfl⟩
  exact boundaryTestChartEndpoint_exactRank n o U e hU s κ k (v y)

/-- The finite-order lift also commutes with the unchanged full scalar-product map. -/
theorem exists_boundaryTestChart_rank_product_factor {Y : Scheme.{0}} [CompactSpace Y]
    (v : Y ⟶ boundaryTestChart n o U e hU s κ k) :
    ∃ (l : ℕ) (w : Y ⟶ rankPullbackThickening (Over.mk p) b n l),
      w ≫ boundaryRankProductMap n o U e hU s κ l n =
        v ≫ boundaryTestChartProjection n o U e hU s κ k ≫
          boundaryTestThickeningMap s κ tests k := by
  obtain ⟨l, w, hw⟩ := exists_boundaryTestChart_rank_factor n o U e hU s κ k v
  refine ⟨l, w, ?_⟩
  change w ≫ rankPullbackMap (Over.mk p) b n l ≫ _ = _
  rw [← Category.assoc, hw, Category.assoc, boundaryTestChartMap_product]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
