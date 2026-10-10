/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalRetainedIntersection
public import FLT.Mazur.WeierstrassSuccessiveXTerminalNodePunctures
public import FLT.Mazur.WeierstrassSuccessiveXResidueNodePunctures
public import FLT.Mazur.WeierstrassSuccessiveXZeroNodePunctures
public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Full terminal compatibility from the actual retained node restrictions

The terminal affine branches and the preceding conic branches are opposite
charts on the same two components. Their overlap identities prove equality on
the entire terminal intersection, including the start-zero case.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "T" => terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp
local notation "ψ" => residueNodeConicMap D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "q" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp
    (Data.b6 e) (Data.factor6 e))
local notation "s₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))


section Positive
variable (hk0 : 0 < start + j)
local notation "N₁" => residueMiddleFirstNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "N₂" => residueMiddleSecondNodeChart D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "neg" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (Polynomial.aeval (-Polynomial.X : Polynomial K))))

/-- Actual branch restrictions prove full compatibility at a positive retained depth. -/
theorem terminalPositiveRetained_compatible_of_branch_restrictions
    {Y : Scheme.{u}} (f : PolygonNodeBranches.node K ⟶ Y)
  (fRet : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
    (Data.b3 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b4 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) (ResidueField R))) ⟶ Y)
  (F₁ F₂ : ProjectiveLine.scheme K ⟶ Y)
  (h₁ : PolygonCyclicAtlas.secondBranch K ≫ f = ProjectiveLine.left K ≫ F₁)
  (h₂ : PolygonCyclicAtlas.firstBranch K ≫ f = ProjectiveLine.right K ≫ F₂)
    (h₃ : middleNodeFirstBranch c hc ≫ N₁ ≫ fRet = ProjectiveLine.right K ≫ F₁)
    (h₄ : middleNodeFirstBranch c hc ≫ N₂ ≫ fRet = neg ≫ ProjectiveLine.left K ≫ F₂) :
    pullback.fst T g ≫ f = pullback.snd T g ≫ fRet := by
  apply (terminalPositiveRetained_compatible_iff hπ data D j hj hk hp hk0 f fRet).mpr
  simp only [Category.assoc]
  constructor
  · rw [residueNodeConicFirstPuncture_branch_assoc,
      residueConicFirstPuncture_node_assoc D (start + j) hk0 hk
        (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) hc,
      h₁, h₃, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun morphism => morphism ≫ F₁)
      (ProjectiveLine.endpointReversal_overlap K).symm
  · rw [residueNodeConicSecondPuncture_branch_assoc,
      residueConicSecondPuncture_node_assoc D (start + j) hk0 hk
        (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) hc,
      h₂, h₄, affineParameterNeg_comp_assoc, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun morphism => morphism ≫ F₂) (ProjectiveLine.overlap_condition K).symm

end Positive

section Zero
variable (hk0 : start + j = 0)
local notation "a" => residue R W.a₁
local notation "V" => zeroResidueFiberIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "E" => conicZeroAffineIso c hc
local notation "N₁" => Iso.hom E ≫ Iso.hom (fullNodeConicParameterIso a c ha) ≫
  fullNodeFirstBranch a c ha ≫ fullFirstNodeChart a c ha ≫ Iso.hom V
local notation "N₂" => Iso.hom E ≫ Iso.hom (fullNodeConicParameterIso (-a) c (IsUnit.neg ha)) ≫
  fullNodeFirstBranch (-a) c (IsUnit.neg ha) ≫ fullSecondNodeChart a c ha ≫ Iso.hom V

/-- The full start-zero terminal intersection uses the original localized conic branches. -/
theorem terminalZeroRetained_compatible_of_branch_restrictions
    {Y : Scheme.{u}} (f : PolygonNodeBranches.node K ⟶ Y)
  (fRet : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
    (Data.b3 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b4 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) (ResidueField R))) ⟶ Y)
  (F₁ F₂ : ProjectiveLine.scheme K ⟶ Y)
  (h₁ : PolygonCyclicAtlas.secondBranch K ≫ f = ProjectiveLine.left K ≫ F₁)
  (h₂ : PolygonCyclicAtlas.firstBranch K ≫ f = ProjectiveLine.right K ≫ F₂)
    (h₃ : N₁ ≫ fRet = ProjectiveLine.right K ≫ F₁)
    (h₄ : N₂ ≫ fRet = ProjectiveLine.left K ≫ F₂) :
    pullback.fst T g ≫ f = pullback.snd T g ≫ fRet := by
  simp only [Category.assoc] at h₃ h₄
  apply (terminalZeroRetained_compatible_iff hπ data D j hj hk hp hk0 f fRet).mpr
  simp only [Category.assoc]
  constructor
  · rw [residueNodeConicFirstPuncture_branch_assoc,
      zeroResidueConicFirstPuncture_node_assoc D (start + j) hk0 hk
        (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) hc,
      h₁, h₃, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun morphism => morphism ≫ F₁)
      (ProjectiveLine.endpointReversal_overlap K).symm
  · rw [residueNodeConicSecondPuncture_branch_assoc,
      zeroResidueConicSecondPuncture_node_assoc D (start + j) hk0 hk
        (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) hc,
      h₂, h₄, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun morphism => morphism ≫ F₂) (ProjectiveLine.overlap_condition K).symm

end Zero

end FLT.Mazur.WeierstrassDividedDepth
