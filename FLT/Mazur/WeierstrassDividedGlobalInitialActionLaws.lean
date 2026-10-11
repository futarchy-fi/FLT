/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalInitialAction

/-!
# Point laws on the whole initial finite model

The actual initial comparison transports naturality, identity, inverse and
associativity, without restricting the modified input to its smooth locus.
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

/-- The point action retains the original smooth parameter's coefficient map. -/
@[reassoc] theorem finiteGlobalInitialPointAction_structure {T : Scheme}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    finiteGlobalInitialPointAction hπ data a b h ≫ base =
      a ≫ integralSmoothStructure W := by
  rw [finiteGlobalStructure, finiteGlobalInitialPointAction_contraction_assoc]
  exact leftSmoothPointAddition_structure W _ _ _

/-- The transported point action commutes with changing the scheme of points. -/
theorem finiteGlobalInitialPointAction_comp {T U : Scheme} (p : U ⟶ T)
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    finiteGlobalInitialPointAction hπ data (p ≫ a) (p ≫ b)
        (by simp only [Category.assoc, h]) =
      p ≫ finiteGlobalInitialPointAction hπ data a b h := by
  have he := WeierstrassGlobalModification.smoothPointAction_comp W (π ^ start)
    (d₀).b3 (d₀).b4 (d₀).b6 (d₀).factor3 (d₀).factor4 (d₀).factor6
    (pow_ne_zero start hπ) p a (b ≫ (e).hom) (by
      change _ = (b ≫ (e).hom) ≫ c ≫ integralCurveStructure W
      rw [Category.assoc, finiteGlobalInitialIso_structure]
      exact h)
  simpa only [finiteGlobalInitialPointAction, Category.assoc] using
    congrArg (fun k => k ≫ (e).inv) he

/-- The initial point action becomes exactly the existing whole action under comparison. -/
@[reassoc] theorem finiteGlobalInitialPointAction_comparison {T : Scheme}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    finiteGlobalInitialPointAction hπ data a b h ≫ (e).hom =
      act a (b ≫ (e).hom)
        (by change _ = (b ≫ (e).hom) ≫ c ≫ integralCurveStructure W
            rw [Category.assoc, finiteGlobalInitialIso_structure]; exact h) := by
  rw [finiteGlobalInitialPointAction, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original smooth zero fixes every point of the whole initial finite model. -/
theorem finiteGlobalInitialPointAction_zero {T : Scheme}
    (b : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n)) :
    finiteGlobalInitialPointAction hπ data (b ≫ base ≫ integralSmoothZero W) b
      (by rw [Category.assoc, Category.assoc, integralSmoothZero_structure,
        Category.comp_id]) = b := by
  apply (cancel_mono (e).hom).mp
  rw [finiteGlobalInitialPointAction_comparison]
  have hb : b ≫ base ≫ integralSmoothZero W =
      (b ≫ (e).hom) ≫ (c ≫ integralCurveStructure W) ≫ integralSmoothZero W := by
    simp only [Category.assoc, finiteGlobalInitialIso_contraction_assoc, finiteGlobalStructure]
  simp only [hb]
  exact WeierstrassGlobalModification.smoothPointAction_zero _ _ _ _ _ _ _ _ _ _ _

/-- The negative parameter undoes translation on all initial finite-model points. -/
theorem finiteGlobalInitialPointAction_neg_cancel {T : Scheme}
    (a : T ⟶ (integralSmoothOpen W).toScheme)
    (b : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (h : a ≫ integralSmoothStructure W = b ≫ base) :
    finiteGlobalInitialPointAction hπ data (a ≫ integralSmoothNegation W)
      (finiteGlobalInitialPointAction hπ data a b h)
      (by rw [Category.assoc, integralSmoothNegation_structure,
        finiteGlobalInitialPointAction_structure]) = b := by
  apply (cancel_mono (e).hom).mp
  simp only [finiteGlobalInitialPointAction_comparison]
  exact WeierstrassGlobalModification.smoothPointAction_neg_cancel _ _ _ _ _ _ _ _ _ _ _ _

/-- Original smooth addition acts associatively on the entire initial finite model. -/
theorem finiteGlobalInitialPointAction_assoc {T : Scheme}
    (a b : T ⟶ (integralSmoothOpen W).toScheme)
    (z : T ⟶ finiteGlobalModel hπ data 0 (Nat.zero_le n))
    (hab : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W)
    (hbz : b ≫ integralSmoothStructure W = z ≫ base) :
    finiteGlobalInitialPointAction hπ data (smoothPairPointAddition W a b hab) z
        (by rw [smoothPairPointAddition_structure]; exact hab.trans hbz) =
      finiteGlobalInitialPointAction hπ data a (finiteGlobalInitialPointAction hπ data b z hbz)
        (by rw [finiteGlobalInitialPointAction_structure]; exact hab) := by
  apply (cancel_mono (e).hom).mp
  simp only [finiteGlobalInitialPointAction_comparison]
  exact WeierstrassGlobalModification.smoothPointAction_assoc _ _ _ _ _ _ _ _ _ _ _ _ _ _

end FLT.Mazur.WeierstrassDividedDepth
