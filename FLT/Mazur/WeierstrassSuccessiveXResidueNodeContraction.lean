/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeBranches
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleNodes
public import FLT.Mazur.WeierstrassSuccessiveXTensorContraction

/-!
# The original contraction on both actual tensor node neighborhoods

In the first ordered node chart the original preceding coordinates become
(u,0); in the second they become (u,-a₁*u). Thus the node comparisons retain
the two original tangent directions and the contraction of the conic branch.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open IsLocalRing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Type*} [CommRing S] (W' : WeierstrassCurve S) (c' : S)

/-- The full horizontal node function annihilates the conic slope coordinate. -/
theorem middleNode_u_mul_v : middleNodeU c' * middleNodeV W'.a₁ c' = 0 := by
  rw [middleNode_v_multiple]
  calc middleNodeU c' * (middleNodeT W'.a₁ c' *
      (algebraMap S (MiddleNodeOpen c') c' * middleNodeZ c')) =
      (middleNodeT W'.a₁ c' * middleNodeU c') *
        (algebraMap S (MiddleNodeOpen c') c' * middleNodeZ c') := by ring
    _ = 0 := by rw [middleNode_incidence, zero_mul]

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "N" => MiddleNodeOpen c
local notation "u" => middleNodeU c
local notation "v" => middleNodeV (WeierstrassCurve.a₁ W₀) c
local notation "f" => tensorPreviousMap W (π ^ k) π b3 b4 b6 K
local notation "x₀" => WeierstrassDilatation.x W (π ^ k) (π * b3) (π * b4) (π ^ 2 * b6)
local notation "y₀" => WeierstrassDilatation.y W (π ^ k) (π * b3) (π * b4) (π ^ 2 * b6)
local notation "E₁" => residueMiddleFirstNodeEquiv D k hk0 hk b3 b4 b6 h3 h4
local notation "E₂" => residueMiddleSecondNodeEquiv D k hk0 hk b3 b4 b6 h3 h4

/-- The actual first node comparison keeps the original tensor slope formula. -/
theorem residueMiddleFirstNodeEquiv_v :
    E₁ (algebraMap T _ (tensorCoord W (π ^ k) π b3 b4 b6 K 1)) = v := by
  simp only [residueMiddleFirstNodeEquiv, AlgEquiv.trans_apply,
    residueMiddleFirstOpenEquiv, PrincipalOpenTransport.equiv_base,
    residueRetainedFiberEquiv_coord, middleFirstNodeEquiv_coord]
  rfl

/-- The second node comparison retains the opposite original tensor tangent slope. -/
theorem residueMiddleSecondNodeEquiv_v :
    E₂ (algebraMap T _ (tensorCoord W (π ^ k) π b3 b4 b6 K 1)) =
      -v - algebraMap K N (residue R W.a₁) := by
  simp only [residueMiddleSecondNodeEquiv, AlgEquiv.trans_apply,
    residueMiddleSecondOpenEquiv, PrincipalOpenTransport.equiv_base,
    residueRetainedFiberEquiv_coord, middleSecondNodeEquiv_base,
    middleTangentSwitch_coord, Matrix.cons_val_one, Matrix.cons_val_zero,
    map_sub, map_neg, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
    middleFirstNodeEquiv_coord]
  rfl

/-- The original horizontal contraction on the first actual node is the retained u. -/
theorem residueFirstNode_previous_x : E₁ (algebraMap T _ (f x₀)) = u := by
  rw [tensorPreviousMap_x, residueMiddleFirstNodeEquiv_u]

/-- The original horizontal contraction on the second actual node is the same u. -/
theorem residueSecondNode_previous_x : E₂ (algebraMap T _ (f x₀)) = u := by
  rw [tensorPreviousMap_x, residueMiddleSecondNodeEquiv_u]

/-- The full first node maps to the zero-slope tangent of the original preceding chart. -/
theorem residueFirstNode_previous_y : E₁ (algebraMap T _ (f y₀)) = 0 := by
  rw [tensorPreviousMap_y, map_mul, map_mul,
    residueMiddleFirstNodeEquiv_u, residueMiddleFirstNodeEquiv_v]
  exact middleNode_u_mul_v W₀ c

/-- The full second node maps to the ordered opposite tangent of that original chart. -/
theorem residueSecondNode_previous_y :
    E₂ (algebraMap T _ (f y₀)) = -algebraMap K N (residue R W.a₁) * u := by
  rw [tensorPreviousMap_y, map_mul, map_mul,
    residueMiddleSecondNodeEquiv_u, residueMiddleSecondNodeEquiv_v,
    mul_sub, mul_neg, middleNode_u_mul_v W₀ c]
  ring

end FLT.Mazur.WeierstrassSuccessiveX
