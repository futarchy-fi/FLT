/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorActionInput
public import FLT.Mazur.WeierstrassDividedGlobalStepExterior

/-!
# Successor action on the full retained-exterior-output domain

The preceding action determines the output-exterior open.
The successor step is unchanged above this entire open, so every input
there has a unique actual lift, with no flatness assumption on restrictions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
  (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))

/-- All successor inputs whose output lies in the preceding exterior. -/
abbrev successorExteriorOutputDomain := pullback (successorActionOutput hπ data j hj a)
  (finitePrecedingExteriorChart hπ data j hj)

/-- The actual successor lift for every input in the full retained-exterior-output domain. -/
def successorExteriorOutputAction : successorExteriorOutputDomain hπ data j hj a ⟶
    finiteGlobalModel hπ data (j + 1) hj :=
  pullback.snd _ _ ≫ finiteSuccessiveRetainedChart hπ data j hj

/-- The lifted retained-exterior-output action contracts to the prescribed preceding action. -/
@[reassoc] theorem successorExteriorOutputAction_step :
    successorExteriorOutputAction hπ data j hj a ≫ finiteGlobalStep hπ data j hj =
      pullback.fst _ _ ≫ successorActionOutput hπ data j hj a := by
  rw [successorExteriorOutputAction, Category.assoc, finiteSuccessiveRetainedChart_step]
  exact pullback.condition.symm

/-- The full unchanged-exterior pullback gives uniqueness on every scheme restriction. -/
theorem successorExteriorOutputAction_unique {X : Scheme.{u}}
    (p : X ⟶ successorExteriorOutputDomain hπ data j hj a)
    (b : X ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ pullback.fst _ _ ≫ successorActionOutput hπ data j hj a) :
    b = p ≫ successorExteriorOutputAction hπ data j hj a := by
  let H := finiteGlobalStep_exterior_isPullback hπ data j hj
  have hc : (p ≫ pullback.snd _ _) ≫ finitePrecedingExteriorChart hπ data j hj =
      b ≫ finiteGlobalStep hπ data j hj := by
    rw [hb, Category.assoc, pullback.condition]
  have he := H.lift_snd (p ≫ pullback.snd _ _) b hc
  have hd := H.lift_fst (p ≫ pullback.snd _ _) b hc
  simp only [Category.comp_id] at hd
  rw [hd] at he
  exact he.symm.trans (Category.assoc _ _ _)

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)
include ha

/-- The retained-exterior-output lift still contracts to the genuine original smooth action. -/
@[reassoc] theorem successorExteriorOutputAction_original :
    successorExteriorOutputAction hπ data j hj a ≫ finiteGlobalContraction hπ data (j + 1) hj =
      pullback.fst _ _ ≫ finiteGlobalActionInput hπ data (j + 1) hj ≫
        leftSmoothFactorAddition W := by
  rw [← finiteGlobalStep_contraction hπ data j hj, successorExteriorOutputAction_step_assoc,
    successorActionOutput_contraction hπ data j hj a ha]

end FLT.Mazur.WeierstrassDividedDepth
