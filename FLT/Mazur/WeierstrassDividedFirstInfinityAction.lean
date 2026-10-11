/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstActionInput
public import FLT.Mazur.WeierstrassDividedGlobalStepOriginal

/-!
# First-successor action on the full infinity-output domain

The existing whole initial action determines the output-infinity open.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)

/-- All first-successor inputs whose initial action lands in the retained infinity chart. -/
abbrev firstInfinityOutputDomain := pullback (firstActionOutput hπ data hn)
  (finiteInfinityChart hπ data 0 (Nat.zero_le n))

/-- The actual successor lift for every input in the full infinity-output domain. -/
def firstInfinityOutputAction : firstInfinityOutputDomain hπ data hn ⟶
    finiteGlobalModel hπ data 1 hn :=
  pullback.snd _ _ ≫ finiteInfinityChart hπ data 1 hn

/-- The lifted infinity-output action contracts to the prescribed initial action. -/
@[reassoc] theorem firstInfinityOutputAction_step :
    firstInfinityOutputAction hπ data hn ≫ finiteGlobalStep hπ data 0 hn =
      pullback.fst _ _ ≫ firstActionOutput hπ data hn := by
  rw [firstInfinityOutputAction, Category.assoc, finiteGlobalStep_infinity]
  exact pullback.condition.symm

/-- The full unchanged-infinity pullback gives uniqueness on every scheme restriction. -/
theorem firstInfinityOutputAction_unique {X : Scheme.{u}}
    (p : X ⟶ firstInfinityOutputDomain hπ data hn)
    (a : X ⟶ finiteGlobalModel hπ data 1 hn)
    (ha : a ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ pullback.fst _ _ ≫ firstActionOutput hπ data hn) :
    a = p ≫ firstInfinityOutputAction hπ data hn := by
  let H := finiteGlobalStep_infinity_isPullback hπ data 0 hn
  have hc : (p ≫ pullback.snd _ _) ≫ finiteInfinityChart hπ data 0 (Nat.zero_le n) =
      a ≫ finiteGlobalStep hπ data 0 hn := by
    rw [ha, Category.assoc, pullback.condition]
  have he := H.lift_snd (p ≫ pullback.snd _ _) a hc
  have hd := H.lift_fst (p ≫ pullback.snd _ _) a hc
  simp only [Category.comp_id] at hd
  rw [hd] at he
  exact he.symm.trans (Category.assoc _ _ _)

/-- The infinity-output lift still contracts to the genuine original smooth action. -/
@[reassoc] theorem firstInfinityOutputAction_original :
    firstInfinityOutputAction hπ data hn ≫ finiteGlobalContraction hπ data 1 hn =
      pullback.fst _ _ ≫ finiteGlobalActionInput hπ data 1 hn ≫
        leftSmoothFactorAddition W := by
  rw [← finiteGlobalStep_contraction hπ data 0 hn, firstInfinityOutputAction_step_assoc,
    firstActionOutput_contraction]

end FLT.Mazur.WeierstrassDividedDepth
