/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTensorOverlap
public import FLT.Mazur.WeierstrassDividedExteriorIntersections
public import FLT.Mazur.TensorOpenChartIntersection

/-!
# The complete adjacent intersection in the finite tensor atlas

The prescribed depth overlap is exactly the intersection of the divided
and successive charts. This retains the entire original integral overlap
and proves that its full tensor extension is cartesian.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j + 1 ≤ n)
open WeierstrassSuccessiveX
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "F" => finiteExterior hπ data E₀ (j + 1) hj

local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e)

omit [IsDomain R] in
/-- The boundary attachment has exactly the image of the original incidence principal open. -/
theorem finiteNextBoundary_range :
    Set.range (nextToX e) = Set.range (xOpenInclusion W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e)) := by
  let v := Scheme.Spec.mapIso (a).toRingEquiv.toCommRingCatIso.op
  have h := v.hom.homeomorph.surjective.range_comp (nextToX e)
  change Set.range (v.hom ≫ nextToX e) = Set.range (nextToX e) at h
  rw [← h]
  change Set.range (Spec.map (CommRingCat.ofHom (a).toRingHom) ≫ nextToX e) = _
  rw [depthOverlap_nextToX]
  rfl

/-- No other points of the newest integral successive chart lie in the divided chart. -/
theorem finiteSuccessive_divided_preimage :
    finiteAtlasMap hπ data E₀ (j + 1) hj 1 ⁻¹' Set.range (Exterior.dividedChart F) =
      Set.range (xOpenInclusion W (π ^ (start + j)) π
        (Data.b3 e) (Data.b4 e) (Data.b6 e)) := by
  rw [← finiteNextBoundary_range data j hj]
  exact (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).newX_divided_preimage hπ e

/-- The full tensor incidence open is the exact adjacent-chart preimage. -/
theorem finiteTensor_depthOverlap_preimage :
    finiteSuccessiveTensorChart hπ data S j hj ⁻¹'
      Set.range (finiteDividedTensorChart hπ data S (j + 1) hj) =
        Set.range (PrincipalOpenTensor.inclusion S t) :=
  TensorOpenChart.chart_principal_preimage S _ _ _ _ _ t
    (finiteSuccessive_divided_preimage hπ data j hj)

/-- The whole original tensor overlap is the cartesian intersection in the finite model. -/
theorem finiteTensor_depthOverlap_isPullback :
    IsPullback ((PrincipalOpenTensor.transitionIso S x t a).hom ≫
      PrincipalOpenTensor.inclusion S x) (PrincipalOpenTensor.inclusion S t)
      (finiteDividedTensorChart hπ data S (j + 1) hj)
      (finiteSuccessiveTensorChart hπ data S j hj) :=
  TensorOpenChart.chart_overlap_isPullback S _ _ _ _ _ x t a
    (finiteSuccessive_depthOverlap hπ data j hj)
    (finiteSuccessive_divided_preimage hπ data j hj)

end FLT.Mazur.WeierstrassDividedDepth
