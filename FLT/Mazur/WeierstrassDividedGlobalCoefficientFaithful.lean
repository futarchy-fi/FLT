/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientOverPoints
public import Mathlib.Algebra.Group.Action.Basic

/-!
# Faithfulness of the intrinsic coefficient-extended action

The coefficient-extended smooth points embed as an orbit with their exact group law.
Thus translation is faithful on the whole finite model, and every coefficient-extended
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

variable (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "base" => pullback.fst
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) (finiteGlobalStructure hπ data j hj)
variable (T : Over (Spec (.of S)))


/-- Embed a coefficient-extended point as its actual retained smooth point over the base. -/
def finiteGlobalSmoothCoefficientOverPoint
    (a : T ⟶ (integralSmoothGroup V).X) :
    T ⟶ Over.mk base :=
  Over.homMk (a.left ≫ finiteGlobalSmoothCoefficientEmbedding S hπ data j hj)
    (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => a.left ≫ f)
          (finiteGlobalSmoothCoefficientEmbedding_structure S hπ data j hj)).trans a.w))

/-- No coefficient-extended smooth point is identified with another by the finite model. -/
theorem finiteGlobalSmoothCoefficientOverPoint_injective :
    Function.Injective (finiteGlobalSmoothCoefficientOverPoint hπ data j hj S T) := by
  intro a b h
  apply Over.OverMorphism.ext
  exact finiteGlobalSmoothCoefficientEmbedding_points_injective hπ data j hj S T.left
    (congrArg Over.Hom.left h)

/-- Translation of the retained smooth orbit is the coefficient-extended group multiplication. -/
theorem finiteGlobalCoefficientOverPointAction_smooth
    (a b : T ⟶ (integralSmoothGroup V).X) :
    a • finiteGlobalSmoothCoefficientOverPoint hπ data j hj S T b =
      finiteGlobalSmoothCoefficientOverPoint hπ data j hj S T (a * b) := by
  apply Over.OverMorphism.ext
  exact finiteGlobalCoefficientPointAction_smoothEmbedding hπ data j hj S a.left b.left
    (a.w.trans b.w.symm)

/-- The full coefficient-extended point group acts faithfully on each actual finite model. -/
instance finiteGlobalCoefficientPointAction_faithful :
    FaithfulSMul (T ⟶ (integralSmoothGroup V).X)
      (T ⟶ Over.mk base) where
  eq_of_smul_eq_smul {a b} h := by
    apply finiteGlobalSmoothCoefficientOverPoint_injective hπ data j hj S T
    have he := h (finiteGlobalSmoothCoefficientOverPoint hπ data j hj S T 1)
    simpa only [finiteGlobalCoefficientOverPointAction_smooth, mul_one] using he

/-- Every extended smooth point permutes all points of the tensor model. -/
def finiteGlobalCoefficientPointPermutation :
    (T ⟶ (integralSmoothGroup V).X) →*
      Equiv.Perm (T ⟶ Over.mk base) :=
  MulAction.toPermHom _ _

/-- The permutation retains the constructed action's actual scheme-valued map. -/
theorem finiteGlobalCoefficientPointPermutation_apply
    (a : T ⟶ (integralSmoothGroup V).X)
    (b : T ⟶ Over.mk base) :
    finiteGlobalCoefficientPointPermutation hπ data j hj S T a b =
      finiteGlobalCoefficientOverPointAction hπ data j hj S T a b := rfl

/-- The coefficient-extended point group injects into the actual permutation group. -/
theorem finiteGlobalCoefficientPointPermutation_injective :
    Function.Injective (finiteGlobalCoefficientPointPermutation hπ data j hj S T) :=
  MulAction.toPerm_injective

/-- Each coefficient-extended subgroup is isomorphic to its subgroup of actual translations. -/
def finiteGlobalCoefficientPointSubgroupEquiv (H : Subgroup (T ⟶ (integralSmoothGroup V).X)) :
    H ≃* H.map (finiteGlobalCoefficientPointPermutation hπ data j hj S T) :=
  H.equivMapOfInjective (finiteGlobalCoefficientPointPermutation hπ data j hj S T)
    (finiteGlobalCoefficientPointPermutation_injective hπ data j hj S T)

/-- In particular, every finite coefficient-extended subgroup retains its exact order. -/
theorem finiteGlobalCoefficientPointSubgroup_card (H : Subgroup (T ⟶ (integralSmoothGroup V).X)) :
    Nat.card (H.map (finiteGlobalCoefficientPointPermutation hπ data j hj S T)) = Nat.card H :=
  Nat.card_congr (finiteGlobalCoefficientPointSubgroupEquiv hπ data j hj S T H).toEquiv.symm

end FLT.Mazur.WeierstrassDividedDepth
