/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentGlobalPunctures
public import FLT.Mazur.WeierstrassDividedOlderGlobalLineExterior

/-!
# Adjacent conic punctures in the actual preceding exterior

The full conic boundary factors through the preceding exterior of the next
chart. Its ordered punctures are the original line-to-exterior maps, with
the reciprocal parameter changes fixed by the original tensor functions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "s₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
local notation "copen" => residueDividedConicOpenEquiv D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "q" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom copen)))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "uNext" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2
local notation "A" => PrincipalOpenTensor.transitionIso K x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "B" => PrincipalOpenTensor.transitionIso K x uNext
  (previousBoundaryEquiv hπ e fData)
local notation "LNext" => residueLineToHorizontal D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)
local notation "g" => olderGlobalTensorChart hπ data K j hj 1 hjNext
local notation "gNext" => olderGlobalTensorChart hπ data K (j + 1) hjNext 0 hjNext
local notation "boundary" => olderGlobalConicBoundary hπ data D j hj 1 hjNext hk0 hk
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹)))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹)))
local notation "p" => ProjectiveLine.overlapLeft K

local notation "ext" => olderGlobalExteriorTensorChart hπ data K (j + 1) hjNext 0 hjNext
local notation "horizontal" =>
  olderGlobalHorizontalToExterior hπ data K (j + 1) hjNext 0 hjNext
local notation "lineExt" => olderGlobalLineToExterior hπ data D (j + 1) hjNext 0 hjNext
  (by omega) hkNext

/-- The entire old conic boundary maps to the actual preceding exterior of the next chart. -/
def adjacentGlobalConicToExterior := q ≫ (B).inv ≫ horizontal

/-- The exterior factor retains the full original conic boundary inclusion. -/
@[reassoc] theorem adjacentGlobalConicToExterior_comp :
    adjacentGlobalConicToExterior hπ data D j hj hk hjNext ≫ ext = boundary := by
  rw [adjacentGlobalConicToExterior, Category.assoc, Category.assoc,
    olderGlobalHorizontalToExterior_comp]
  exact (adjacentGlobalConicBoundary_horizontal hπ data D j hj hk0 hk hjNext).symm

/-- The first conic puncture is the actual zero-slope line map into the preceding exterior. -/
@[reassoc] theorem adjacentGlobalConicFirst_exterior :
    s₁ ≫ adjacentGlobalConicToExterior hπ data D j hj hk hjNext =
      ρ₁ ≫ lineExt 0 (by simp) := by
  apply (cancel_mono ext).mp
  rw [Category.assoc, adjacentGlobalConicToExterior_comp hπ data D j hj hk0 hk hjNext,
    Category.assoc, olderGlobalLineToExterior_comp]
  exact adjacentGlobalConicFirst_line hπ data D j hj hk0 hk hjNext hkNext

/-- The opposite conic puncture is the actual opposite line map with its negative scale. -/
@[reassoc] theorem adjacentGlobalConicSecond_exterior :
    s₂ ≫ adjacentGlobalConicToExterior hπ data D j hj hk hjNext =
      ρ₂ ≫ lineExt (-residue R W.a₁) (by simp) := by
  apply (cancel_mono ext).mp
  rw [Category.assoc, adjacentGlobalConicToExterior_comp hπ data D j hj hk0 hk hjNext,
    Category.assoc, olderGlobalLineToExterior_comp]
  exact adjacentGlobalConicSecond_line hπ data D j hj hk0 hk hjNext hkNext

/-- The first complete conic parameter and the next line have the same global puncture. -/
@[reassoc] theorem adjacentGlobalConicFirstParameter_line :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc))) ≫
      olderGlobalMiddleConicFirstParameter hπ data D j hj 1 hjNext hk0 hk = ρ₁ ≫ p ≫
        olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext 0 hjNext (by omega) hkNext := by
  rw [olderGlobalConicFirst_puncture hπ data D j hj 1 hjNext hk0 hk (by omega)]
  exact adjacentGlobalConicFirst_line hπ data D j hj hk0 hk hjNext hkNext

/-- The opposite complete conic parameter retains the same signed line attachment. -/
@[reassoc] theorem adjacentGlobalConicSecondParameter_line :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc))) ≫
      olderGlobalMiddleConicSecondParameter hπ data D j hj 1 hjNext hk0 hk = ρ₂ ≫ p ≫
        olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext 0 hjNext (by omega) hkNext := by
  rw [olderGlobalConicSecond_puncture hπ data D j hj 1 hjNext hk0 hk (by omega)]
  exact adjacentGlobalConicSecond_line hπ data D j hj hk0 hk hjNext hkNext

end FLT.Mazur.WeierstrassDividedDepth
