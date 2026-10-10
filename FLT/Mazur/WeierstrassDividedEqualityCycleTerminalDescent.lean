/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityTerminalNodeDescent

public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Terminal-node descent in the cyclic orientation

The terminal projective line has reversed endpoints in the equality cycle.
These descent statements use that orientation and the horizontal charts of
its two neighboring components, preserving both tangent scales.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D s hs hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D s hs hk hp
local notation "ρ" => ProjectiveLine.endpointReversal K
local notation "ν" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom (conicParameterNeg c))))

/-- The incoming terminal node glues the preceding zero to the reversed terminal infinity. -/
theorem equalityCycleTerminalFirst_exists_unique_desc (a : Kˣ) {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ Y)
    (w : ProjectiveLine.zero K ≫ g = ProjectiveLine.infinity K ≫ f) :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      middleParameterConicBranch c ≫ d = q₁ ≫ ρ ≫ f ∧
      ProjectiveLine.chartScaling K a ≫ middleParameterLineBranch c ≫ d =
        ProjectiveLine.left K ≫ g := by
  apply equalityTerminalFirstNode_exists_unique_desc data D s hs hk hp a
  rw [ProjectiveLine.zero_endpointReversal_assoc]
  simpa only [ProjectiveLine.zero, Category.assoc] using w.symm

/-- The outgoing node glues the reversed terminal zero to the following infinity. -/
theorem equalityCycleTerminalSecond_exists_unique_desc (a : Kˣ) {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ Y)
    (w : ProjectiveLine.zero K ≫ f = ProjectiveLine.infinity K ≫ g) :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      middleParameterConicBranch c ≫ d = ν ≫ q₂ ≫ ρ ≫ f ∧
      ProjectiveLine.chartScaling K a ≫ middleParameterLineBranch c ≫ d =
        ProjectiveLine.right K ≫ g := by
  apply equalityTerminalSecondNode_exists_unique_desc data D s hs hk hp a
  rw [ProjectiveLine.infinity_endpointReversal_assoc]
  simpa only [ProjectiveLine.infinity, Category.assoc] using w

end FLT.Mazur.WeierstrassDividedDepth
