/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAction
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientSmoothOrbit

/-!
# The actual smooth orbit in the complete coefficient-sheared model

The independently constructed original smooth embedding survives the full
gluing comparison. The existing action on it is exactly intrinsic addition.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (algebraMap R S)
local notation "f" => integralSmoothStructure V
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "E" => coefficientShearGluedIso hπ data S r j hj
local notation "D" => coefficientShearActionDomainMap hπ data S r j hj
local notation "emb" => finiteGlobalSmoothCoefficientEmbedding S hπ data j hj

/-- The original full smooth orbit, retained by the complete equation-gluing comparison. -/
def coefficientShearSmoothEmbedding : (integralSmoothOpen V).toScheme ⟶
    coefficientShearGlued hπ data S r j hj := emb ≫ (E).inv

local notation "B" => coefficientShearSmoothEmbedding hπ data S r j hj

/-- Reconstruction recovers the independent original coefficient smooth embedding. -/
@[reassoc] theorem coefficientShearSmoothEmbedding_reconstruction : B ≫ (E).hom = emb := by
  rw [coefficientShearSmoothEmbedding, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The full original smooth orbit preserves the coefficient structure. -/
@[reassoc] theorem coefficientShearSmoothEmbedding_structure : B ≫ g = f := by
  rw [coefficientShearGluedStructure, coefficientShearSmoothEmbedding_reconstruction_assoc,
    finiteGlobalSmoothCoefficientEmbedding_structure]

instance coefficientShearSmoothEmbedding_isOpenImmersion : IsOpenImmersion B := by
  unfold coefficientShearSmoothEmbedding
  infer_instance

/-- On every scheme of pairs the sheared action reconstructs the original coefficient action. -/
theorem coefficientShearAction_pair {T : Scheme.{u}}
    (p : T ⟶ (integralSmoothOpen V).toScheme)
    (q : T ⟶ coefficientShearGlued hπ data S r j hj) (hpq : p ≫ f = q ≫ g) :
    pullback.lift p q hpq ≫ coefficientShearAction hπ data S r j hj =
      finiteGlobalCoefficientPointAction hπ data j hj S p (q ≫ (E).hom)
        (by simpa only [Category.assoc, coefficientShearGluedStructure] using hpq) ≫
          (E).inv := by
  rw [coefficientShearAction, ← Category.assoc, ← Category.assoc]
  apply congrArg (· ≫ (E).inv)
  change (pullback.lift p q hpq ≫ D) ≫
    finiteGlobalCoefficientPointAction hπ data j hj S _ _ _ = _
  rw [← finiteGlobalCoefficientPointAction_comp]
  simp only [Category.assoc, coefficientShearActionDomainMap_parameter,
    coefficientShearActionDomainMap_model, pullback.lift_fst, pullback.lift_snd_assoc]

/-- The complete sheared action on the original smooth orbit is intrinsic smooth addition. -/
theorem coefficientShearAction_smoothEmbedding {T : Scheme.{u}}
    (p q : T ⟶ (integralSmoothOpen V).toScheme) (hpq : p ≫ f = q ≫ f) :
    pullback.lift p (q ≫ B)
        (by rw [Category.assoc, coefficientShearSmoothEmbedding_structure]; exact hpq) ≫
      coefficientShearAction hπ data S r j hj =
        smoothPairPointAddition V p q hpq ≫ B := by
  rw [coefficientShearAction_pair]
  simp only [Category.assoc, coefficientShearSmoothEmbedding_reconstruction]
  rw [finiteGlobalCoefficientPointAction_smoothEmbedding]
  exact Category.assoc _ _ _

end FLT.Mazur.WeierstrassDividedDepth
