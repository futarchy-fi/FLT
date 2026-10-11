/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalInitialAction

/-!
# Geometry and uniqueness of the initial finite action

The actual comparison induces an isomorphism of complete action products.
Thus the initial finite action is smooth and surjective. Contraction detects
all competitors of flat reference morphisms into the initial finite model.
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

/-- The initial comparison identifies the complete two action products. -/
def finiteGlobalInitialActionProductIso :
    finiteGlobalActionProduct hπ data 0 (Nat.zero_le n) ≅
      pullback (integralSmoothStructure W) (c ≫ integralCurveStructure W) :=
  asIso (pullback.map _ _ _ _ (𝟙 _) (e).hom (𝟙 _)
    (by simp) (by rw [Category.comp_id, finiteGlobalInitialIso_structure]))

/-- The product comparison retains the original smooth parameter. -/
@[reassoc] theorem finiteGlobalInitialActionProductIso_fst :
    (finiteGlobalInitialActionProductIso hπ data).hom ≫ pullback.fst _ _ =
      pullback.fst (integralSmoothStructure W) base := by
  simp [finiteGlobalInitialActionProductIso]

/-- The product comparison uses precisely the whole initial model comparison. -/
@[reassoc] theorem finiteGlobalInitialActionProductIso_snd :
    (finiteGlobalInitialActionProductIso hπ data).hom ≫ pullback.snd _ _ =
      pullback.snd (integralSmoothStructure W) base ≫ (e).hom := by
  simp [finiteGlobalInitialActionProductIso]

/-- The whole initial action is the single-step action transported by actual isomorphisms. -/
theorem finiteGlobalInitialAction_eq :
    finiteGlobalInitialAction hπ data =
      (finiteGlobalInitialActionProductIso hπ data).hom ≫
        WeierstrassGlobalModification.smoothAction W (π ^ start)
          (d₀).b3 (d₀).b4 (d₀).b6 (d₀).factor3 (d₀).factor4 (d₀).factor6
          (pow_ne_zero start hπ) ≫ (e).inv := by
  unfold finiteGlobalInitialAction finiteGlobalInitialPointAction
    WeierstrassGlobalModification.smoothPointAction
  rw [← Category.assoc]
  congr 1

/-- The action on the entire initial finite model is smooth. -/
instance finiteGlobalInitialAction_smooth : Smooth (finiteGlobalInitialAction hπ data) := by
  rw [finiteGlobalInitialAction_eq]
  infer_instance

/-- The whole initial finite action is surjective, including onto exceptional points. -/
instance finiteGlobalInitialAction_surjective :
    Surjective (finiteGlobalInitialAction hπ data) := by
  rw [finiteGlobalInitialAction_eq]
  infer_instance

/-- Flat-reference uniqueness on the actual entire initial finite model. -/
theorem finiteGlobalInitial_contraction_ext_of_flat {T : Scheme}
    (p : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n)) [Flat p]
    (f : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (hf : f ≫ finiteGlobalContraction hπ data 0 (Nat.zero_le n) =
      p ≫ finiteGlobalContraction hπ data 0 (Nat.zero_le n)) : f = p := by
  apply (cancel_mono (e).hom).mp
  apply WeierstrassGlobalModification.contraction_ext_of_flat _ _ _ _ _ _ _ _ _
    (p ≫ (e).hom)
  simpa only [Category.assoc, finiteGlobalInitialIso_contraction] using hf

/-- The constructed whole initial action is the unique lift of its original contraction. -/
theorem finiteGlobalInitialAction_unique
    (f : finiteGlobalActionProduct hπ data 0 (Nat.zero_le n) ⟶
      finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (hf : f ≫ finiteGlobalContraction hπ data 0 (Nat.zero_le n) =
      finiteGlobalActionInput hπ data 0 (Nat.zero_le n) ≫ leftSmoothFactorAddition W) :
    f = finiteGlobalInitialAction hπ data := by
  apply finiteGlobalInitial_contraction_ext_of_flat hπ data (finiteGlobalInitialAction hπ data)
  rw [hf, finiteGlobalInitialAction_contraction]

end FLT.Mazur.WeierstrassDividedDepth
