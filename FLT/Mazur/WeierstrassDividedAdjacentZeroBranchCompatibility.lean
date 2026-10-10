/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentPunctureCompatibility
public import FLT.Mazur.WeierstrassDividedAdjacentNodePunctures
public import FLT.Mazur.ProjectiveLineEndpointReversal
public import FLT.Mazur.WeierstrassSuccessiveXZeroNodePunctures

/-!
# Start-zero adjacent compatibility from the actual full node branches

The two original Laurent punctures detect equality on the complete adjacent
intersection. The zero-node conic parameters retain their given orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX WeierstrassModificationX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
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
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr
local notation "gNext" => olderGlobalTensorChart hπ data K (j + 1) hjNext r hr
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
variable (hp : 2 * (start + j + 1) < depth)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp
    (Data.b6 e) (Data.factor6 e))
local notation "s₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
variable {Y : Scheme.{u}}
  (f : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
    (Data.b3 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b4 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) (ResidueField R))) ⟶ Y)
  (fNext : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + (j + 1))) π
    (Data.b3 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩))
    (Data.b4 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩))
    (Data.b6 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) (ResidueField R))) ⟶ Y)

variable (hk0 : start + j = 0) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (hcNext : residue R (Data.b6 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
local notation "cNext" => residue R (Data.b6 fData)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "a" => residue R W.a₁
local notation "V" => zeroResidueFiberIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "E" => conicZeroAffineIso c hc
local notation "N₁" => Iso.hom E ≫ Iso.hom (fullNodeConicParameterIso a c ha) ≫
  fullNodeFirstBranch a c ha ≫ fullFirstNodeChart a c ha ≫ Iso.hom V
local notation "N₂" => Iso.hom E ≫ Iso.hom (fullNodeConicParameterIso (-a) c (IsUnit.neg ha)) ≫
  fullNodeFirstBranch (-a) c (IsUnit.neg ha) ≫ fullSecondNodeChart a c ha ≫ Iso.hom V
local notation "M₁" => residueMiddleFirstNodeChart D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)
local notation "M₂" => residueMiddleSecondNodeChart D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)
/-- Actual branch restrictions on two common projective components imply full compatibility. -/
theorem adjacentZero_compatible_of_branch_restrictions
    (F₁ F₂ : ProjectiveLine.scheme K ⟶ Y)
    (h₁ : N₁ ≫ f = ProjectiveLine.right K ≫ F₁)
    (h₂ : N₂ ≫ f = ProjectiveLine.left K ≫ F₂)
    (h₃ : ProjectiveLine.chartScaling K (tangent)⁻¹ ≫
      middleNodeSecondBranch cNext hcNext ≫ M₁ ≫ fNext = ProjectiveLine.left K ≫ F₁)
    (h₄ : ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫
      middleNodeSecondBranch cNext hcNext ≫ M₂ ≫ fNext = ProjectiveLine.right K ≫ F₂) :
    pullback.fst g gNext ≫ f = pullback.snd g gNext ≫ fNext := by
  simp only [Category.assoc] at h₁ h₂
  apply (adjacentZeroNormalized_compatible_iff
    hπ data D j hj hk hjNext r hr hp f fNext hk0).mpr
  simp only [Category.assoc]
  constructor
  · rw [zeroResidueConicFirstPuncture_node_assoc D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) hc,
      adjacentConicFirstPuncture_nextNode_assoc hπ data D j hj hk hjNext hkNext hcNext,
      h₁, h₃, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun morphism => morphism ≫ F₁) (ProjectiveLine.endpointReversal_overlap K)
  · rw [zeroResidueConicSecondPuncture_node_assoc D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) hc,
      adjacentConicSecondPuncture_nextNode_assoc hπ data D j hj hk hjNext hkNext hcNext,
      h₂, h₄, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun morphism => morphism ≫ F₂) (ProjectiveLine.overlap_condition K)

end FLT.Mazur.WeierstrassDividedDepth
