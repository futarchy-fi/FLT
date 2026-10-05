/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedLineTwist

/-!
# Multiplication of the actual ideal-power modules

Multiplication factors through the sum power, as verified on affine sections.
Its compatibility with adjacent inclusions supplies the relations needed to
multiply the associated-graded cokernels.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility
open ModuleSheafTensor

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- The ring multiplication of two power ideals, with target the sum power. -/
def idealPowerMul (a b : ℕ) :
    tensor (idealModule (I ^ a)) (idealModule (I ^ b)) ⟶ idealModule (I ^ (a + b)) := by
  have := idealModule_coherent (I ^ a)
  have := idealModule_coherent (I ^ b)
  refine affineFactor (scalarAction (I ^ a) (idealModule (I ^ b)) ≫
    idealModuleι (I ^ b)) (idealModuleι (I ^ (a + b))) ?_
  intro V
  rintro _ ⟨t, rfl⟩
  change (idealModuleι (I ^ b)).app V.1
    ((scalarAction (I ^ a) (idealModule (I ^ b))).app V.1 t) ∈ _
  obtain ⟨t, rfl⟩ := (affineSectionsEquiv
    (idealModule (I ^ a)) (idealModule (I ^ b)) V.1 V.2).surjective t
  rw [show LinearMap.range ((idealModuleι (I ^ (a + b))).val.app (op V.1)).hom =
      (I.ideal V) ^ (a + b) from by
    ext x
    exact Set.ext_iff.mp (idealModuleι_range (I ^ (a + b)) V) x]
  induction t using TensorProduct.inductionOn with
  | tmul s t =>
    rw [affineSectionsEquiv_tmul, scalarAction_pure, Hom.app_smul]
    change (show Γ(X, V.1) from (idealModuleι (I ^ a)).app V.1 s) *
      (show Γ(X, V.1) from (idealModuleι (I ^ b)).app V.1 t) ∈ _
    rw [pow_add]
    exact Ideal.mul_mem_mul
      (by rw [← idealModuleAffineEquiv_val]; exact (idealModuleAffineEquiv _ V s).property)
      (by rw [← idealModuleAffineEquiv_val]; exact (idealModuleAffineEquiv _ V t).property)
  | add s t hs ht => simpa only [map_add] using Submodule.add_mem _ hs ht

/-- Multiplication retains its original map to the structure sheaf. -/
@[reassoc (attr := simp)]
lemma idealPowerMul_inclusion (a b : ℕ) :
    idealPowerMul I a b ≫ idealModuleι (I ^ (a + b)) =
      scalarAction (I ^ a) (idealModule (I ^ b)) ≫ idealModuleι (I ^ b) := by
  unfold idealPowerMul
  apply affineFactor_comp

/-- On pure tensors, the constructed map is ordinary ring multiplication. -/
lemma idealPowerMul_pure (a b : ℕ) (U : X.Opens)
    (s : Γ(idealModule (I ^ a), U)) (t : Γ(idealModule (I ^ b), U)) :
    (idealModuleι (I ^ (a + b))).app U
      ((idealPowerMul I a b).app U (pure _ _ U s t)) =
        (show Γ(X, U) from (idealModuleι (I ^ a)).app U s) *
          (show Γ(X, U) from (idealModuleι (I ^ b)).app U t) := by
  have h := congrArg (fun f ↦ f.app U (pure _ _ U s t)) (idealPowerMul_inclusion I a b)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, scalarAction_pure,
    Hom.app_smul] at h
  exact h

/-- Any two power products with the same total exponent agree under inclusions. -/
lemma idealPowerMul_natural (a b c d : ℕ) (ha : a ≤ c) (hb : b ≤ d) :
    ModuleSheafTensor.map (idealMap (I := I ^ c) (J := I ^ a)
      (fun _ ↦ Ideal.pow_le_pow_right ha))
      (idealMap (I := I ^ d) (J := I ^ b) (fun _ ↦ Ideal.pow_le_pow_right hb)) ≫
        idealPowerMul I a b =
      idealPowerMul I c d ≫ idealMap (I := I ^ (c + d)) (J := I ^ (a + b))
        (fun _ ↦ Ideal.pow_le_pow_right (Nat.add_le_add ha hb)) := by
  apply (cancel_mono (idealModuleι (I ^ (a + b)))).mp
  apply ModuleSheafTensor.hom_ext
  intro U s t
  simp only [Category.assoc, idealMap_comp, Hom.comp_app, ConcreteCategory.comp_apply,
    map_pure, idealPowerMul_pure]
  congr 1
  · exact congrArg (fun f ↦ f.app U s)
      (idealMap_comp (I := I ^ c) (J := I ^ a) (fun _ ↦ Ideal.pow_le_pow_right ha))
  · exact congrArg (fun f ↦ f.app U t)
      (idealMap_comp (I := I ^ d) (J := I ^ b) (fun _ ↦ Ideal.pow_le_pow_right hb))

/-- The inclusion from the next total power, using a supplied exponent equality. -/
def idealPowerStepAt (a b : ℕ) (h : a = b + 1) :
    idealModule (I ^ a) ⟶ idealModule (I ^ b) :=
  idealMap (fun _ ↦ Ideal.pow_le_pow_right (by omega))

/-- Increasing the left degree gives a product in the next total power. -/
@[reassoc]
lemma idealPowerMul_step_left (a b : ℕ) :
    ModuleSheafTensor.map (idealStep I a) (𝟙 _) ≫ idealPowerMul I a b =
      idealPowerMul I (a + 1) b ≫ idealPowerStepAt I (a + 1 + b) (a + b) (by omega) := by
  have h := idealPowerMul_natural I a b (a + 1) b (Nat.le_succ a) le_rfl
  have he : idealMap (I := I ^ b) (J := I ^ b) (fun _ ↦ Ideal.pow_le_pow_right le_rfl) =
      𝟙 _ := by apply (cancel_mono (idealModuleι (I ^ b))).mp; simp
  simpa only [he, idealStep, idealPowerStepAt] using h

/-- Increasing the right degree gives a product in the next total power. -/
@[reassoc]
lemma idealPowerMul_step_right (a b : ℕ) :
    ModuleSheafTensor.map (𝟙 _) (idealStep I b) ≫ idealPowerMul I a b =
      idealPowerMul I a (b + 1) ≫ idealPowerStepAt I (a + (b + 1)) (a + b) (by omega) := by
  have h := idealPowerMul_natural I a b a (b + 1) le_rfl (Nat.le_succ b)
  have he : idealMap (I := I ^ a) (J := I ^ a) (fun _ ↦ Ideal.pow_le_pow_right le_rfl) =
      𝟙 _ := by apply (cancel_mono (idealModuleι (I ^ a))).mp; simp
  simpa only [he, idealStep, idealPowerStepAt] using h

omit [IsLocallyNoetherian X] in
/-- The next-power inclusion is killed by the graded quotient. -/
@[reassoc (attr := simp)]
lemma idealPowerStepAt_quotient (a b : ℕ) (h : a = b + 1) :
    idealPowerStepAt I a b h ≫ cokernel.π (idealStep I b) = 0 := by
  subst a
  exact cokernel.condition (idealStep I b)

end FLT.Mazur.IdealAdicQuotient
