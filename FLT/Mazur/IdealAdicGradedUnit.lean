/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedAssociativity

/-!
# The unit of the actual associated-graded ideal multiplication

The inverse of the degree-zero ideal inclusion supplies the unit map. Its
left and right unit identities are proved on the actual quotient sheaves.
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

/-- The zeroth ideal-power module is the structure module. -/
def idealPowerZeroIso : idealModule (I ^ 0) ≅ structureModule X := by
  have : IsIso (idealModuleι (I ^ 0)) := by
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    infer_instance
  exact asIso (idealModuleι (I ^ 0))

/-- The unit is the ordinary section of the zeroth power followed by its quotient. -/
def idealGradedUnit : structureModule X ⟶ idealGraded I 0 :=
  (idealPowerZeroIso I).inv ≫ cokernel.π (idealStep I 0)

/-- The constructed unit represents the original ring section. -/
@[simp]
lemma idealPowerZeroIso_inv_app (U : X.Opens) (r : Γ(X, U)) :
    (idealModuleι (I ^ 0)).app U ((idealPowerZeroIso I).inv.app U r) = r :=
  congrArg (fun f ↦ f.app U r) (idealPowerZeroIso I).inv_hom_id

variable [IsLocallyNoetherian X]

/-- Left multiplication by the degree-zero unit is the tensor unitor. -/
lemma idealGradedMul_unit_left (n : ℕ) :
    ModuleSheafTensor.map (idealGradedUnit I) (𝟙 (idealGraded I n)) ≫
      idealGradedMul I 0 n ≫ idealGradedReindex I (Nat.zero_add n) =
        (leftUnitor (idealGraded I n)).hom := by
  apply (cancel_epi (ModuleSheafTensor.map (𝟙 (structureModule X))
    (cokernel.π (idealStep I n)))).mp
  apply ModuleSheafTensor.hom_ext
  intro U r s
  change Γ(X, U) at r
  have hm (i j : ℕ) := idealGradedMul_pure I i j
  have hr {i j : ℕ} (e : i = j) := idealGradedReindex_app I e
  simp only [idealGraded] at hm hr
  simp only [idealGraded, structureModule, Hom.comp_app, ConcreteCategory.comp_apply,
    map_pure, Hom.id_app,
    ConcreteCategory.id_apply, idealGradedUnit, hm,
    hr, leftUnitor_pure]
  rw [← Hom.app_smul]
  congr 1
  apply FLT.Mazur.ModuleSubobjectCoverEquality.app_injective (idealModuleι (I ^ n)) U
  rw [idealPowerReindex_app, idealPowerMul_pure]
  erw [idealPowerZeroIso_inv_app I U r, Hom.app_smul]
  rfl

/-- Right multiplication by the degree-zero unit is the tensor unitor. -/
lemma idealGradedMul_unit_right (n : ℕ) :
    ModuleSheafTensor.map (𝟙 (idealGraded I n)) (idealGradedUnit I) ≫
      idealGradedMul I n 0 = (rightUnitor (idealGraded I n)).hom := by
  apply (cancel_epi (ModuleSheafTensor.map (cokernel.π (idealStep I n))
    (𝟙 (structureModule X)))).mp
  apply ModuleSheafTensor.hom_ext
  intro U s r
  change Γ(X, U) at r
  have hm (i j : ℕ) := idealGradedMul_pure I i j
  simp only [idealGraded] at hm
  simp only [idealGraded, structureModule, Hom.comp_app, ConcreteCategory.comp_apply,
    map_pure, Hom.id_app,
    ConcreteCategory.id_apply, idealGradedUnit, hm]
  erw [rightUnitor_pure (cokernel (idealStep I n)) U r]
  rw [← Hom.app_smul]
  congr 1
  apply FLT.Mazur.ModuleSubobjectCoverEquality.app_injective (idealModuleι (I ^ n)) U
  erw [idealPowerMul_pure I n 0 U s ((idealPowerZeroIso I).inv.app U r)]
  erw [idealPowerZeroIso_inv_app I U r, Hom.app_smul]
  exact mul_comm (show Γ(X, U) from (idealModuleι (I ^ n)).app U s)
    (show Γ(X, U) from r)

end FLT.Mazur.IdealAdicQuotient
