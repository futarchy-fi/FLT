/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedConicBoundaryGeometryAllDepths
public import FLT.Mazur.WeierstrassSuccessiveXResidueNodePunctures
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing

/-!
# Original adjacent punctures in the next retained node branches

The complete tensor transition restricts to the scaled horizontal branch
of the next node. Both original tangent scales are retained.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

variable (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "g₁" => conicBoundaryFirst W₀ c ha hc
local notation "g₂" => conicBoundarySecond W₀ c ha hc
local notation "copen" => residueDividedConicOpenEquiv D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "xNext" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "uNext" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2
local notation "B" => PrincipalOpenTensor.transitionIso K xNext uNext
  (previousBoundaryEquiv hπ e fData)
local notation "LNext" => residueLineToHorizontal D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)
local notation "Q" => ResidueDividedOpen (W := W) (π := π) (start + j)
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "ρ₁" => PolygonScaledReciprocal.reciprocal (tangent)⁻¹
local notation "ρ₂" => PolygonScaledReciprocal.reciprocal (-tangent)⁻¹

local notation "q" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (AlgEquiv.toAlgHom copen)))
local notation "s₁" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g₁))
local notation "s₂" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g₂))
local notation "cNext" => residue R (Data.b6 fData)
variable (hcNext : residue R (Data.b6 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
local notation "N₁" => residueMiddleFirstNodeChart D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)
local notation "N₂" => residueMiddleSecondNodeChart D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)

/-- The first original Laurent puncture has the next node's scaled horizontal projection. -/
@[reassoc] theorem adjacentConicFirstPuncture_nextNode :
    s₁ ≫ q ≫ Iso.inv B ≫ PrincipalOpenTensor.inclusion K uNext =
      ProjectiveLine.overlapRight K ≫ ProjectiveLine.chartScaling K (tangent)⁻¹ ≫
        middleNodeSecondBranch cNext hcNext ≫ N₁ := by
  rw [← Category.assoc, adjacentConicFirstLine_boundary_spec_anyDepth
    hπ data D j hj hk hjNext hkNext]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [residueLineToHorizontal_comp, ProjectiveLine.scaledReciprocal_overlap_assoc,
    residueMiddleFirstNodeChart_lineBranch]

/-- The opposite puncture preserves the negative reciprocal horizontal scale. -/
@[reassoc] theorem adjacentConicSecondPuncture_nextNode :
    s₂ ≫ q ≫ Iso.inv B ≫ PrincipalOpenTensor.inclusion K uNext =
      ProjectiveLine.overlapRight K ≫ ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫
        middleNodeSecondBranch cNext hcNext ≫ N₂ := by
  rw [← Category.assoc, adjacentConicSecondLine_boundary_spec_anyDepth
    hπ data D j hj hk hjNext hkNext]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [residueLineToHorizontal_comp, ProjectiveLine.scaledReciprocal_overlap_assoc,
    residueMiddleSecondNodeChart_lineBranch]

end FLT.Mazur.WeierstrassDividedDepth
