/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedBoundary
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedBoundary
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensorIntersection

/-!
# Whole adjacent chart and conic intersections in the equation gluing

The actual full retained charts intersect in the preceding conic incidence
open. Restricting to the entire conic preserves this complete intersection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
include hj hjNext
local notation "d" => data (Fin.mk (j + 1) (by omega))
local notation "e" => data (Fin.mk (j + 2) (by omega))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j) * π)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "v" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t
  (overlapEquiv W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "B" => PrincipalOpenTensor.transitionIso S x v (adjacentBoundaryEquiv hπ d e)
local notation "old" => coefficientShearRetainedTensorChart hπ data S r
  (j + 2 + m) hm (Fin.mk j (by omega))
local notation "next" => coefficientShearRetainedTensorChart hπ data S r
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega))

variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "E" => tensorShearConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp g3 g4 hr
local notation "N" => coefficientShearAdjacentConicToNext hπ d e S r hs hp hr

local notation "x₀" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "A₀" => PrincipalOpenTensor.transitionIso S x₀ t
  (depthOverlapEquiv W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "B₀" => PrincipalOpenTensor.transitionIso S x₀ v (previousBoundaryEquiv hπ d e)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data S j hj m hm
local notation "gNext" => olderGlobalTensorChart hπ data S (j + 1) hjNext m hm
local notation "G" => coefficientShearGluedIso hπ data S r (j + 2 + m) hm

set_option maxHeartbeats 600000 in
-- Indexed component presentations require additional elaboration heartbeats.
/-- The conic open is the complete intersection of the actual two retained chart embeddings. -/
theorem coefficientShearAdjacentGluedCharts_isPullback :
    IsPullback ((E).hom ≫ PrincipalOpenTensor.inclusion S t)
      N old next := by
  have sq := adjacentRetainedGlobalTensor_isPullback hπ data S j hj hjNext m hm
  have hboundary := congrArg (fun f => f ≫ (G).hom)
    (coefficientShearAdjacentGlued_conic_boundary hπ data S r j hj hjNext m hm hs hp hr)
  simp only [Category.assoc, coefficientShearRetainedTensorChart_adjacent_old hπ data S r
    j hj m hm, coefficientShearRetainedTensorChart_adjacent_next hπ data S r
    j hjNext m hm] at hboundary
  apply sq.of_iso' ((E) ≪≫ (A₀)) (Iso.refl _) (Iso.refl _) (G)
  · simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.refl_hom, Category.comp_id]
  · simp only [Iso.trans_hom, Iso.refl_hom, Category.comp_id]
    apply (cancel_mono gNext).mp
    simp only [Category.assoc]
    rw [← adjacentRetainedGlobalTensor_boundary hπ data S j hj hjNext m hm]
    simpa only [Iso.hom_inv_id_assoc] using hboundary
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientShearRetainedTensorChart_adjacent_old hπ data S r j hj m hm).symm
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (coefficientShearRetainedTensorChart_adjacent_next hπ data S r j hjNext m hm).symm

local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "inc" => PrincipalOpenTransport.inclusion
  (conicT (WeierstrassCurve.a₁ U) (algebraMap R S (Data.b6 d)))
local notation "C" => tensorShearConicImmersion W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp g3 g4 hr

set_option maxHeartbeats 600000 in
-- Indexed component presentations require additional elaboration heartbeats.
/-- The entire preceding conic meets the whole next chart exactly in its incidence open. -/
theorem coefficientShearAdjacentGluedFullConic_isPullback :
    IsPullback N inc next
      (coefficientShearRetainedConic hπ data S r (j + 2 + m) hm ⟨j, by omega⟩
        hs hp g3 g4 hr) := by
  have sq := coefficientShearAdjacentGluedCharts_isPullback hπ data S r j hj hjNext
    m hm hs hp hr
  rw [tensorShearConicBoundaryIso_inclusion] at sq
  have inner : IsPullback (𝟙 _) inc (inc ≫ C) C :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  rw [← coefficientShearRetainedTensorChart_conic]
  simpa only [Category.id_comp] using inner.paste_horiz sq.flip

end FLT.Mazur.WeierstrassDividedDepth
