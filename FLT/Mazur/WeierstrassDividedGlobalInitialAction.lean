/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalInitialComparison
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothActionUnique
public import FLT.Mazur.WeierstrassGlobalModificationActionAssociativity
public import FLT.Mazur.WeierstrassGlobalModificationActionSmooth

/-!
# The whole action on the initial finite global model

Transport the constructed action through the actual initial comparison.
This acts on the complete finite-stage-zero source, including exceptional
points, and agrees with the previous action on original smooth inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => finiteGlobalInitialIso hπ data
local notation "c" => WeierstrassGlobalModification.contraction W (π ^ start)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
  (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) (pow_ne_zero start hπ)
local notation "base" => finiteGlobalStructure hπ data 0 (Nat.zero_le n)
local notation "act" => WeierstrassGlobalModification.smoothPointAction W (π ^ start)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
  (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) (pow_ne_zero start hπ)
open WeierstrassIntegralChart

/-- The inverse initial comparison preserves the exact original contraction. -/
@[reassoc] theorem finiteGlobalInitialIso_inv_contraction :
    (e).inv ≫ finiteGlobalContraction hπ data 0 (Nat.zero_le n) = c := by
  rw [← finiteGlobalInitialIso_contraction, Iso.inv_hom_id_assoc]

/-- The initial comparison is over the original coefficient scheme. -/
@[reassoc] theorem finiteGlobalInitialIso_structure :
    (e).hom ≫ (c ≫ integralCurveStructure W) = base := by
  rw [finiteGlobalInitialIso_contraction_assoc]
  rfl

/-- The inverse initial comparison is also over the original coefficient scheme. -/
@[reassoc] theorem finiteGlobalInitialIso_inv_structure :
    (e).inv ≫ base = c ≫ integralCurveStructure W := by
  rw [finiteGlobalStructure, finiteGlobalInitialIso_inv_contraction_assoc]

/-- Actual action on any point of the whole initial finite global model. -/
def finiteGlobalInitialPointAction {T : Scheme}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n) :=
  act a (b ≫ (e).hom)
    (by change _ = (b ≫ (e).hom) ≫ c ≫ integralCurveStructure W
        rw [Category.assoc, finiteGlobalInitialIso_structure]; exact h) ≫ (e).inv

/-- The transported action contracts to the actual original whole-cubic action. -/
@[reassoc] theorem finiteGlobalInitialPointAction_contraction {T : Scheme}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    finiteGlobalInitialPointAction hπ data a b h ≫
        finiteGlobalContraction hπ data 0 (Nat.zero_le n) =
      leftSmoothPointAddition W a
        (b ≫ finiteGlobalContraction hπ data 0 (Nat.zero_le n)) h := by
  simp only [finiteGlobalInitialPointAction, Category.assoc,
    finiteGlobalInitialIso_inv_contraction,
    WeierstrassGlobalModification.smoothPointAction_contraction,
    finiteGlobalInitialIso_contraction]

/-- The initial finite action on its entire prescribed product. -/
def finiteGlobalInitialAction : finiteGlobalActionProduct hπ data 0 (Nat.zero_le n) ⟶
    finiteGlobalModel hπ data 0 (Nat.zero_le n) :=
  finiteGlobalInitialPointAction hπ data (pullback.fst _ _) (pullback.snd _ _)
    pullback.condition

/-- The whole initial finite action lies over the prescribed original input action. -/
@[reassoc] theorem finiteGlobalInitialAction_contraction :
    finiteGlobalInitialAction hπ data ≫ finiteGlobalContraction hπ data 0 (Nat.zero_le n) =
      finiteGlobalActionInput hπ data 0 (Nat.zero_le n) ≫ leftSmoothFactorAddition W :=
  finiteGlobalInitialPointAction_contraction hπ data _ _ _

/-- The whole initial action restricts to exactly the previously constructed smooth action. -/
@[reassoc] theorem finiteGlobalInitialAction_originalSmooth :
    finiteGlobalOriginalSmoothPair hπ data 0 (Nat.zero_le n) ≫
      finiteGlobalInitialAction hπ data =
        finiteGlobalOriginalSmoothAction hπ data 0 (Nat.zero_le n) :=
  finiteGlobalAction_originalSmooth_unique hπ data 0 (Nat.zero_le n)
    (finiteGlobalInitialAction hπ data) (finiteGlobalInitialAction_contraction hπ data)

end FLT.Mazur.WeierstrassDividedDepth
