/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstActionInput
public import FLT.Mazur.WeierstrassDividedGlobalStepExterior

/-!
# First-successor action on the full retained-exterior-output domain

The existing whole initial action determines the output-exterior open.
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

/-- All first-successor inputs whose output lies in the preceding exterior. -/
abbrev firstExteriorOutputDomain := pullback (firstActionOutput hπ data hn)
  (finitePrecedingExteriorChart hπ data 0 hn)

/-- The actual successor lift for every input in the full retained-exterior-output domain. -/
def firstExteriorOutputAction : firstExteriorOutputDomain hπ data hn ⟶
    finiteGlobalModel hπ data 1 hn :=
  pullback.snd _ _ ≫ finiteSuccessiveRetainedChart hπ data 0 hn

/-- The lifted retained-exterior-output action contracts to the prescribed initial action. -/
@[reassoc] theorem firstExteriorOutputAction_step :
    firstExteriorOutputAction hπ data hn ≫ finiteGlobalStep hπ data 0 hn =
      pullback.fst _ _ ≫ firstActionOutput hπ data hn := by
  rw [firstExteriorOutputAction, Category.assoc, finiteSuccessiveRetainedChart_step]
  exact pullback.condition.symm

/-- The full unchanged-exterior pullback gives uniqueness on every scheme restriction. -/
theorem firstExteriorOutputAction_unique {X : Scheme.{u}}
    (p : X ⟶ firstExteriorOutputDomain hπ data hn)
    (a : X ⟶ finiteGlobalModel hπ data 1 hn)
    (ha : a ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ pullback.fst _ _ ≫ firstActionOutput hπ data hn) :
    a = p ≫ firstExteriorOutputAction hπ data hn := by
  let H := finiteGlobalStep_exterior_isPullback hπ data 0 hn
  have hc : (p ≫ pullback.snd _ _) ≫ finitePrecedingExteriorChart hπ data 0 hn =
      a ≫ finiteGlobalStep hπ data 0 hn := by
    rw [ha, Category.assoc, pullback.condition]
  have he := H.lift_snd (p ≫ pullback.snd _ _) a hc
  have hd := H.lift_fst (p ≫ pullback.snd _ _) a hc
  simp only [Category.comp_id] at hd
  rw [hd] at he
  exact he.symm.trans (Category.assoc _ _ _)

/-- The retained-exterior-output lift still contracts to the genuine original smooth action. -/
@[reassoc] theorem firstExteriorOutputAction_original :
    firstExteriorOutputAction hπ data hn ≫ finiteGlobalContraction hπ data 1 hn =
      pullback.fst _ _ ≫ finiteGlobalActionInput hπ data 1 hn ≫
        leftSmoothFactorAddition W := by
  rw [← finiteGlobalStep_contraction hπ data 0 hn, firstExteriorOutputAction_step_assoc,
    firstActionOutput_contraction]

end FLT.Mazur.WeierstrassDividedDepth
