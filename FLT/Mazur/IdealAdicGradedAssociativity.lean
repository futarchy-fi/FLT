/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedMultiplication

/-!
# Associativity and commutativity of ideal-graded multiplication

Degree transports are equality maps, and all identities are proved on the
actual quotient sheaves by cancellation of tensorized quotient projections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CoherentIdealIntersection
open ModuleSheafTensor ModuleSheafTensorAssociator

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Equality transport of the actual ideal-power module. -/
def idealPowerReindex {a b : ℕ} (h : a = b) :
    idealModule (I ^ a) ⟶ idealModule (I ^ b) :=
  by subst b; exact 𝟙 _

/-- Equality transport of the actual graded quotient. -/
def idealGradedReindex {a b : ℕ} (h : a = b) : idealGraded I a ⟶ idealGraded I b :=
  by subst b; exact 𝟙 _

/-- Reindexing leaves the original ring section unchanged. -/
@[reassoc (attr := simp)]
lemma idealPowerReindex_inclusion {a b : ℕ} (h : a = b) :
    idealPowerReindex I h ≫ idealModuleι (I ^ b) = idealModuleι (I ^ a) := by
  subst b
  simp [idealPowerReindex]

/-- Reindexing commutes with the actual quotient projection. -/
@[reassoc]
lemma idealPowerReindex_projection {a b : ℕ} (h : a = b) :
    idealPowerReindex I h ≫ cokernel.π (idealStep I b) =
      cokernel.π (idealStep I a) ≫ idealGradedReindex I h := by
  subst b
  simp only [idealPowerReindex, idealGradedReindex, idealGraded,
    Category.id_comp, Category.comp_id]

/-- Section form of the ring inclusion compatibility. -/
@[simp]
lemma idealPowerReindex_app {a b : ℕ} (h : a = b) (U : X.Opens)
    (s : Γ(idealModule (I ^ a), U)) :
    (idealModuleι (I ^ b)).app U ((idealPowerReindex I h).app U s) =
      (idealModuleι (I ^ a)).app U s :=
  congrArg (fun f ↦ f.app U s) (idealPowerReindex_inclusion I h)

/-- Section form of quotient compatibility. -/
lemma idealGradedReindex_app {a b : ℕ} (h : a = b) (U : X.Opens)
    (s : Γ(idealModule (I ^ a), U)) :
    (idealGradedReindex I h).app U ((cokernel.π (idealStep I a)).app U s) =
      (cokernel.π (idealStep I b)).app U ((idealPowerReindex I h).app U s) :=
  (congrArg (fun f ↦ f.app U s) (idealPowerReindex_projection I h)).symm

variable [IsLocallyNoetherian X]

/-- Associativity before passage to quotients, with the necessary degree transport. -/
lemma idealPowerMul_assoc (a b c : ℕ) :
    ModuleSheafTensor.map (idealPowerMul I a b) (𝟙 _) ≫ idealPowerMul I (a + b) c =
      (associator (idealModule (I ^ a)) (idealModule (I ^ b))
        (idealModule (I ^ c))).hom ≫
      ModuleSheafTensor.map (𝟙 _) (idealPowerMul I b c) ≫ idealPowerMul I a (b + c) ≫
        idealPowerReindex I (Nat.add_assoc a b c).symm := by
  apply (cancel_mono (idealModuleι (I ^ ((a + b) + c)))).mp
  apply left_hom_ext
  intro U s t v
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, associator_hom_pure, idealPowerReindex_app, idealPowerMul_pure]
  exact mul_assoc (show Γ(X, U) from (idealModuleι (I ^ a)).app U s)
    (show Γ(X, U) from (idealModuleι (I ^ b)).app U t)
    (show Γ(X, U) from (idealModuleι (I ^ c)).app U v)

/-- The actual graded multiplication is associative. -/
lemma idealGradedMul_assoc (a b c : ℕ) :
    ModuleSheafTensor.map (idealGradedMul I a b) (𝟙 _) ≫ idealGradedMul I (a + b) c =
      (associator (idealGraded I a) (idealGraded I b) (idealGraded I c)).hom ≫
        ModuleSheafTensor.map (𝟙 _) (idealGradedMul I b c) ≫ idealGradedMul I a (b + c) ≫
          idealGradedReindex I (Nat.add_assoc a b c).symm := by
  apply (cancel_epi (ModuleSheafTensor.map
    (ModuleSheafTensor.map (cokernel.π (idealStep I a)) (cokernel.π (idealStep I b)))
    (cokernel.π (idealStep I c)))).mp
  apply left_hom_ext
  intro U s t v
  have hm (i j : ℕ) := idealGradedMul_pure I i j
  have hr {i j : ℕ} (e : i = j) := idealGradedReindex_app I e
  simp only [idealGraded] at hm hr
  simp only [idealGraded, Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, associator_hom_pure, hm,
    hr]
  have h := congrArg (fun f ↦ f.app U (pure _ _ U (pure _ _ U s t) v))
    (idealPowerMul_assoc I a b c)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, associator_hom_pure] at h
  exact congrArg ((cokernel.π (idealStep I ((a + b) + c))).app U) h

/-- Commutativity before passage to quotients. -/
lemma idealPowerMul_comm (a b : ℕ) :
    idealPowerMul I a b = (comm (idealModule (I ^ a)) (idealModule (I ^ b))).hom ≫
      idealPowerMul I b a ≫ idealPowerReindex I (Nat.add_comm b a) := by
  apply (cancel_mono (idealModuleι (I ^ (a + b)))).mp
  apply ModuleSheafTensor.hom_ext
  intro U s t
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, comm_hom_pure,
    idealPowerReindex_app, idealPowerMul_pure]
  exact mul_comm (show Γ(X, U) from (idealModuleι (I ^ a)).app U s)
    (show Γ(X, U) from (idealModuleι (I ^ b)).app U t)

/-- The actual graded multiplication is commutative. -/
lemma idealGradedMul_comm (a b : ℕ) :
    idealGradedMul I a b = (comm (idealGraded I a) (idealGraded I b)).hom ≫
      idealGradedMul I b a ≫ idealGradedReindex I (Nat.add_comm b a) := by
  apply idealGraded_tensor_hom_ext I a b
  apply ModuleSheafTensor.hom_ext
  intro U s t
  have hm (i j : ℕ) := idealGradedMul_pure I i j
  have hr {i j : ℕ} (e : i = j) := idealGradedReindex_app I e
  simp only [idealGraded] at hm hr
  simp only [idealGraded, Hom.comp_app, ConcreteCategory.comp_apply, map_pure, comm_hom_pure,
    hm, hr]
  have h := congrArg (fun f ↦ f.app U (pure _ _ U s t)) (idealPowerMul_comm I a b)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, comm_hom_pure] at h
  exact congrArg ((cokernel.π (idealStep I (a + b))).app U) h

end FLT.Mazur.IdealAdicQuotient
