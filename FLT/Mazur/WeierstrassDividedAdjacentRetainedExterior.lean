/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentRetainedPunctures
public import FLT.Mazur.WeierstrassDividedOlderGlobalLineExterior

/-!
# The adjacent punctures in the actual exterior after every later retention

The full original conic boundary still maps to the preceding exterior of
the next chart. Both ordered punctures are the actual original line maps
there, with their reciprocal scales unchanged.
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
  (r : ℕ) (hr : j + 2 + r ≤ n)
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
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (j + 1) hjNext r hr
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹)))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹)))
local notation "p" => ProjectiveLine.overlapLeft K

local notation "boundary" => adjacentRetainedConicBoundary hπ data D j hj hk0 hk r hr
local notation "ext" => olderGlobalExteriorTensorChart hπ data K (j + 1) hjNext r hr
local notation "horizontal" =>
  olderGlobalHorizontalToExterior hπ data K (j + 1) hjNext r hr
local notation "lineExt" => olderGlobalLineToExterior hπ data D (j + 1) hjNext r hr
  (by omega) hkNext

/-- The old conic boundary maps into the actual next preceding exterior at every later stage. -/
def adjacentRetainedConicToExterior := q ≫ (B).inv ≫ horizontal

/-- The exterior factor retains the original full global conic boundary at every later stage. -/
@[reassoc] theorem adjacentRetainedConicToExterior_comp :
    adjacentRetainedConicToExterior hπ data D j hj hk hjNext r hr ≫ ext = boundary := by
  rw [adjacentRetainedConicToExterior, Category.assoc, Category.assoc,
    olderGlobalHorizontalToExterior_comp]
  exact (adjacentRetainedConicBoundary_horizontal hπ data D j hj hk0 hk hjNext r hr).symm

/-- The first puncture is the original retained zero-slope line map into that exterior. -/
@[reassoc] theorem adjacentRetainedConicFirst_exterior :
    s₁ ≫ adjacentRetainedConicToExterior hπ data D j hj hk hjNext r hr =
      ρ₁ ≫ lineExt 0 (by simp) := by
  apply (cancel_mono ext).mp
  rw [Category.assoc,
    adjacentRetainedConicToExterior_comp hπ data D j hj hk0 hk hjNext r hr,
    Category.assoc, olderGlobalLineToExterior_comp]
  exact adjacentRetainedConicFirst_line hπ data D j hj hk0 hk hjNext hkNext r hr

/-- The opposite puncture is the original retained opposite line with its negative scale. -/
@[reassoc] theorem adjacentRetainedConicSecond_exterior :
    s₂ ≫ adjacentRetainedConicToExterior hπ data D j hj hk hjNext r hr =
      ρ₂ ≫ lineExt (-residue R W.a₁) (by simp) := by
  apply (cancel_mono ext).mp
  rw [Category.assoc,
    adjacentRetainedConicToExterior_comp hπ data D j hj hk0 hk hjNext r hr,
    Category.assoc, olderGlobalLineToExterior_comp]
  exact adjacentRetainedConicSecond_line hπ data D j hj hk0 hk hjNext hkNext r hr

end FLT.Mazur.WeierstrassDividedDepth
