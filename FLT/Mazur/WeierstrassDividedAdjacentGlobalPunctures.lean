/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineBoundaryGeometry
public import FLT.Mazur.WeierstrassDividedAdjacentTensorBoundary
public import FLT.Mazur.WeierstrassDividedOlderConicPunctures
public import FLT.Mazur.WeierstrassSuccessiveXResidueConicIntegralBoundary

/-!
# Adjacent conic and line punctures in their first common global model

The original ordered conic punctures agree with the next ordered line
punctures, with the two original reciprocal scales. The comparison takes
place in the actual global model and retains all boundary functions.
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

/-- The full original conic boundary factors through the next actual horizontal boundary. -/
@[reassoc] theorem adjacentGlobalConicBoundary_horizontal :
    boundary = q ≫ (B).inv ≫ PrincipalOpenTensor.inclusion K uNext ≫ gNext := by
  rw [← olderGlobalConicBoundary_transition hπ data D j hj 1 hjNext hk0 hk,
    ← residueDividedConicOpen_spec_boundary D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e),
    Category.assoc, adjacentGlobalTensor_boundary hπ data K j hj hjNext]

/-- The first old conic puncture is the next zero-slope line puncture in the actual global model. -/
@[reassoc] theorem adjacentGlobalConicFirst_line :
    s₁ ≫ boundary = ρ₁ ≫ p ≫
      olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext 0 hjNext (by omega) hkNext := by
  rw [adjacentGlobalConicBoundary_horizontal hπ data D j hj hk0 hk hjNext]
  rw [← Category.assoc, adjacentConicFirstLine_boundary_spec hπ data D j hj hk0 hk
    hjNext hkNext]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [residueLineToHorizontal_comp_assoc]
  rfl

/-- The opposite puncture retains its negative reciprocal scale in the actual global model. -/
@[reassoc] theorem adjacentGlobalConicSecond_line :
    s₂ ≫ boundary = ρ₂ ≫ p ≫
      olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext 0 hjNext (by omega) hkNext := by
  rw [adjacentGlobalConicBoundary_horizontal hπ data D j hj hk0 hk hjNext]
  rw [← Category.assoc, adjacentConicSecondLine_boundary_spec hπ data D j hj hk0 hk
    hjNext hkNext]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [residueLineToHorizontal_comp_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
