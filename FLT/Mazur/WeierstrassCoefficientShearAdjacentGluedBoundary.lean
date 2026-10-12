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

public import FLT.Mazur.WeierstrassDividedAdjacentCorrectedBoundary
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
import all FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentChartMap
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentIntersection

/-!
# The full adjacent conic boundary in the complete equation gluing

At any later common depth the preceding conic incidence open and the next
horizontal open have exactly the same map into the actual glued model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "v" => coord W (π ^ (start + j + 1)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t
  (overlapEquiv W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "B" => PrincipalOpenTensor.transitionIso S x v (adjacentBoundaryEquiv hπ d e)
local notation "old" => coefficientShearRetainedTensorChart hπ data S r
  (j + 2 + m) hm (Fin.mk j (by omega))
local notation "next" => coefficientShearRetainedTensorChart hπ data S r
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega))

/-- Both actual retained chart embeddings agree on the complete corrected boundary. -/
@[reassoc] theorem coefficientShearAdjacentGlued_boundary :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t ≫ old =
      (B).inv ≫ PrincipalOpenTensor.inclusion S v ≫ next := by
  apply (cancel_mono (coefficientShearGluedIso hπ data S r (j + 2 + m) hm).hom).mp
  simp only [Category.assoc, coefficientShearRetainedTensorChart_adjacent_old hπ data S r
    j hj m hm, coefficientShearRetainedTensorChart_adjacent_next hπ data S r j hjNext m hm]
  exact adjacentRetainedCorrectedGlobal_boundary hπ data S j hj hjNext m hm

variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "E" => tensorShearConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp g3 g4 hr
local notation "N" => coefficientShearAdjacentConicToNext hπ d e S r hs hp hr

set_option maxHeartbeats 600000 in
-- Indexed tensor localization presentations need additional elaboration heartbeats.
/-- The entire preceding conic open agrees with the actual next horizontal open. -/
@[reassoc] theorem coefficientShearAdjacentGlued_conic_boundary :
    (E).hom ≫ PrincipalOpenTensor.inclusion S t ≫ old =
      N ≫ next := by
  rw [coefficientShearAdjacentConicToNext_factor_assoc]
  erw [← coefficientShearAdjacentGlued_boundary hπ data S r j hj hjNext m hm]
  erw [Iso.hom_inv_id_assoc]
  rfl

local notation "U" => rootShearCurve (W.map (algebraMap R S)) r

set_option maxHeartbeats 600000 in
-- The two indexed conic maps expose different localization presentations.
/-- The comparison retains the original whole conic map, not just its puncture points. -/
@[reassoc] theorem coefficientShearAdjacentGlued_conic :
    PrincipalOpenTransport.inclusion (conicT (WeierstrassCurve.a₁ U)
        (algebraMap R S (Data.b6 d))) ≫
      coefficientShearRetainedConic hπ data S r (j + 2 + m) hm ⟨j, by omega⟩
        hs hp g3 g4 hr = N ≫ next := by
  rw [← coefficientShearRetainedTensorChart_conic, ← Category.assoc,
    ← tensorShearConicBoundaryIso_inclusion, Category.assoc]
  exact coefficientShearAdjacentGlued_conic_boundary hπ data S r j hj hjNext m hm hs hp hr

end FLT.Mazur.WeierstrassDividedDepth
