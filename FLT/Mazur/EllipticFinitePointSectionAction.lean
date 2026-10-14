/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteModificationPointExtension
public import FLT.Mazur.EllipticE0GeometricGroup
public import FLT.Mazur.WeierstrassDividedGlobalOriginalSmoothPoints

/-!
# Equivariance of unrestricted proper point extensions

The actual E₀ action on every finite modification carries the unique section
of an arbitrary original point to the section of its arithmetic translate.
Only generic smoothness is used; closed specialization may still meet a node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A K))
local notation "f" => finiteGlobalStructure hπ data j hj
local notation "B" => finiteGlobalSmoothEmbedding hπ data j hj

/-- The integral smooth parameter and every proper extension have the same base. -/
theorem finitePointSection_action_condition (P : ellipticE0 A W)
    (Q : (W.map (algebraMap A K)).toProjective.Point) :
    (e0SmoothSectionEquiv A W P).left ≫ integralSmoothStructure W =
      finitePointSection A hπ data j hj Q ≫ f := by
  rw [finitePointSection_structure]
  exact (e0SmoothSectionEquiv A W P).w

/-- Proper extensions respect the existing E₀ action, including on points outside E₀. -/
theorem finitePointSection_add (P : ellipticE0 A W)
    (Q : (W.map (algebraMap A K)).toProjective.Point) :
    finiteGlobalPointAction hπ data j hj (e0SmoothSectionEquiv A W P).left
        (finitePointSection A hπ data j hj Q)
        (finitePointSection_action_condition A hπ data j hj P Q) =
      finitePointSection A hπ data j hj (P.val + Q) := by
  apply finitePointSection_unique A hπ data j hj
  · rw [finiteGlobalPointAction_structure]
    exact (e0SmoothSectionEquiv A W P).w
  · rw [← finiteGlobalPointAction_comp]
    have hp : q ≫ (e0SmoothSectionEquiv A W P).left = projectiveToSmooth W P.val :=
      smoothIntegralPointSection_generic A W P.val P.property
    simp only [hp, finitePointSection_generic]
    rw [finiteGlobalPointAction_smoothEmbedding hπ data j hj _ _
      (by rw [projectiveToSmooth_structure, projectiveToSmooth_structure])]
    congr 1
    exact (congrArg (fun t => t.left) (projectiveToSmoothOver_add W P.val Q)).symm

/-- Each successor contracts every unrestricted section to its unique previous extension. -/
@[reassoc] theorem finitePointSection_step (hnext : j + 1 ≤ n)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    finitePointSection A hπ data (j + 1) hnext P ≫ finiteGlobalStep hπ data j hnext =
      finitePointSection A hπ data j (Nat.le_of_succ_le hnext) P := by
  apply finitePointSection_unique A hπ data j (Nat.le_of_succ_le hnext) P
  · rw [Category.assoc, finiteGlobalStep_structure, finitePointSection_structure]
  · rw [← Category.assoc, finitePointSection_generic, Category.assoc,
      finiteGlobalSmoothEmbedding_step]

end FLT.Mazur.WeierstrassDividedDepth
