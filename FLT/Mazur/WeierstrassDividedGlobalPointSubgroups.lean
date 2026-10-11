/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalOverPointAction
public import Mathlib.Algebra.Group.Action.Basic

/-!
# Faithfulness and finite subgroups of the original point action

The original smooth points embed as an orbit with their exact group law.
Thus translation is faithful on the whole finite model, and every original
finite subgroup keeps its cardinality in the permutation group.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

variable (j : ℕ) (hj : j ≤ n)

variable (T : Over (Spec (.of R)))


/-- Embed an original point as its actual retained smooth point over the base. -/
def finiteGlobalSmoothOverPoint
    (a : T ⟶ (integralSmoothGroup W).X) :
    T ⟶ Over.mk (finiteGlobalStructure hπ data j hj) :=
  Over.homMk (a.left ≫ finiteGlobalSmoothEmbedding hπ data j hj)
    (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => a.left ≫ f)
          (finiteGlobalSmoothEmbedding_structure hπ data j hj)).trans a.w))

/-- No original smooth point is identified with another by the finite model. -/
theorem finiteGlobalSmoothOverPoint_injective :
    Function.Injective (finiteGlobalSmoothOverPoint hπ data j hj T) := by
  intro a b h
  apply Over.OverMorphism.ext
  exact finiteGlobalSmoothEmbedding_points_injective hπ data j hj T.left
    (congrArg Over.Hom.left h)

/-- Translation of the retained smooth orbit is the original group multiplication. -/
theorem finiteGlobalOverPointAction_smooth
    (a b : T ⟶ (integralSmoothGroup W).X) :
    a • finiteGlobalSmoothOverPoint hπ data j hj T b =
      finiteGlobalSmoothOverPoint hπ data j hj T (a * b) := by
  apply Over.OverMorphism.ext
  exact finiteGlobalPointAction_smoothEmbedding hπ data j hj a.left b.left
    (a.w.trans b.w.symm)

/-- The full original point group acts faithfully on each actual finite model. -/
instance finiteGlobalPointAction_faithful :
    FaithfulSMul (T ⟶ (integralSmoothGroup W).X)
      (T ⟶ Over.mk (finiteGlobalStructure hπ data j hj)) where
  eq_of_smul_eq_smul {a b} h := by
    apply finiteGlobalSmoothOverPoint_injective hπ data j hj T
    have he := h (finiteGlobalSmoothOverPoint hπ data j hj T 1)
    simpa only [finiteGlobalOverPointAction_smooth, mul_one] using he

/-- Every original smooth point acts as an actual permutation of all finite-model points. -/
def finiteGlobalPointPermutation :
    (T ⟶ (integralSmoothGroup W).X) →*
      Equiv.Perm (T ⟶ Over.mk (finiteGlobalStructure hπ data j hj)) :=
  MulAction.toPermHom _ _

/-- The permutation retains the constructed action's actual scheme-valued map. -/
theorem finiteGlobalPointPermutation_apply
    (a : T ⟶ (integralSmoothGroup W).X)
    (b : T ⟶ Over.mk (finiteGlobalStructure hπ data j hj)) :
    finiteGlobalPointPermutation hπ data j hj T a b =
      finiteGlobalOverPointAction hπ data j hj T a b := rfl

/-- The original point group injects into the actual permutation group. -/
theorem finiteGlobalPointPermutation_injective :
    Function.Injective (finiteGlobalPointPermutation hπ data j hj T) :=
  MulAction.toPerm_injective

/-- Each original subgroup is isomorphic to its subgroup of actual translations. -/
def finiteGlobalPointSubgroupEquiv (H : Subgroup (T ⟶ (integralSmoothGroup W).X)) :
    H ≃* H.map (finiteGlobalPointPermutation hπ data j hj T) :=
  H.equivMapOfInjective (finiteGlobalPointPermutation hπ data j hj T)
    (finiteGlobalPointPermutation_injective hπ data j hj T)

/-- In particular, every finite original subgroup retains its exact order. -/
theorem finiteGlobalPointSubgroup_card (H : Subgroup (T ⟶ (integralSmoothGroup W).X)) :
    Nat.card (H.map (finiteGlobalPointPermutation hπ data j hj T)) = Nat.card H :=
  Nat.card_congr (finiteGlobalPointSubgroupEquiv hπ data j hj T H).toEquiv.symm

end FLT.Mazur.WeierstrassDividedDepth
