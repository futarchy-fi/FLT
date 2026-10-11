/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothEmbedding
public import FLT.Mazur.WeierstrassLeftSmoothRestriction
public import FLT.Mazur.WeierstrassSmoothAdditionIdentity
public import FLT.Mazur.WeierstrassSmoothAssociativity

/-!
# Lift the original action on the unchanged smooth open of every finite model

The original smooth group multiplication has an actual lift into every finite
global modification. It agrees with enlarged whole-cubic addition under the
original contraction and with every actual preceding modification step.
The action over exceptional charts is a separate construction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassDividedDepth

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)

/-- The actual action lifted on the original smooth pair open of the finite modification. -/
def finiteGlobalOriginalSmoothAction :
    smoothFactorProduct W ⟶ finiteGlobalModel hπ data j hj :=
  smoothFactorAddition W ≫ finiteGlobalSmoothEmbedding hπ data j hj

/-- The lifted smooth-open action contracts to exactly the whole-cubic action. -/
@[reassoc] theorem finiteGlobalOriginalSmoothAction_contraction :
    finiteGlobalOriginalSmoothAction hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      smoothFactorsToLeftSmooth W ≫ leftSmoothFactorAddition W := by
  rw [finiteGlobalOriginalSmoothAction, Category.assoc,
    finiteGlobalSmoothEmbedding_contraction, smoothFactorsToLeftSmooth_addition]

/-- Its coefficient morphism is the coefficient morphism of the original first input. -/
@[reassoc] theorem finiteGlobalOriginalSmoothAction_structure :
    finiteGlobalOriginalSmoothAction hπ data j hj ≫ finiteGlobalStructure hπ data j hj =
      smoothFactorProductStructure W := by
  rw [finiteGlobalOriginalSmoothAction, Category.assoc,
    finiteGlobalSmoothEmbedding_structure, smoothFactorAddition_structure]
  rfl

/-- The original zero section acts by the original finite smooth embedding. -/
@[reassoc] theorem finiteGlobalOriginalSmoothAction_zero :
    smoothFactorLeftZero W ≫ finiteGlobalOriginalSmoothAction hπ data j hj =
      finiteGlobalSmoothEmbedding hπ data j hj := by
  rw [finiteGlobalOriginalSmoothAction, smoothFactorAddition_left_identity_assoc]

/-- The lifted action is associative on the original smooth triple product. -/
theorem finiteGlobalOriginalSmoothAction_assoc :
    smoothFactorAddFirstPair W ≫ finiteGlobalOriginalSmoothAction hπ data j hj =
      smoothFactorAddLastPair W ≫ finiteGlobalOriginalSmoothAction hπ data j hj := by
  have h := congrArg (fun f => f ≫ finiteGlobalSmoothEmbedding hπ data j hj)
    (smoothFactorAddition_assoc W)
  simpa only [finiteGlobalOriginalSmoothAction, smoothFactorTripleAddLeft,
    smoothFactorTripleAddRight, Category.assoc] using h

/-- Each original finite step retains this actual smooth-open action. -/
@[reassoc] theorem finiteGlobalOriginalSmoothAction_step (hnext : j + 1 ≤ n) :
    finiteGlobalOriginalSmoothAction hπ data (j + 1) hnext ≫ finiteGlobalStep hπ data j hnext =
      finiteGlobalOriginalSmoothAction hπ data j (Nat.le_of_succ_le hnext) := by
  rw [finiteGlobalOriginalSmoothAction, Category.assoc, finiteGlobalSmoothEmbedding_step]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
