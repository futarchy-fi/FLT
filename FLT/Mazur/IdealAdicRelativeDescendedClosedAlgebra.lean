/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeDescendedScalars

/-!
# Multiplication and relative scalars under closed total recovery

Equip the actual closed total additive sheaf with the original coefficient
operations. The descended pushforward comparison retains both the product
and the global relative module structure, with its original underlying map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.IdealAdicGradedClosedAction

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeDescendedCoefficientSheaf
attribute [local irreducible] relativeDescendedCoefficientPushforward

/-- The original coefficient product on the actual closed total additive sheaf. -/
def closedTotalCoefficientMul (U : X.Opens)
    (s t : (closedTotalSheaf J f).obj.obj (.op U)) :
    (closedTotalSheaf J f).obj.obj (.op U) :=
  AdditiveSheafMultiplication.mul _ _ (closedTotalSheafIso J f) (.op U) s t

/-- The coefficient unit on the actual closed total additive sheaf. -/
def closedTotalCoefficientOne (U : X.Opens) :
    (closedTotalSheaf J f).obj.obj (.op U) :=
  AdditiveSheafMultiplication.one _ _ (closedTotalSheafIso J f) (.op U)

/-- The original relative action on the actual closed total additive sheaf. -/
def closedTotalRelativeModule : SheafOfModules (relativeScalarSheaf J f) :=
  AdditiveSheafModuleTransport.moduleSheaf _ (relativeCoefficientModuleSheaf J f)
    (closedTotalSheafIso J f)

/-- Relative scalars leave the original underlying closed total additive sheaf unchanged. -/
lemma closedTotalRelativeModule_underlying :
    (SheafOfModules.toSheaf (relativeScalarSheaf J f)).obj (closedTotalRelativeModule J f) =
      closedTotalSheaf J f := rfl

/-- Closed total recovery is linear for the global relative scalar action. -/
def relativeDescendedClosedTotalLinearIso :
    relativeDescendedRelativeModule J f ≅ closedTotalRelativeModule J f :=
  relativeDescendedRelativeModuleIso J f ≪≫
    (AdditiveSheafModuleTransport.moduleIso _ (relativeCoefficientModuleSheaf J f)
      (closedTotalSheafIso J f)).symm

/-- The linear comparison retains the actual descended closed total comparison. -/
lemma relativeDescendedClosedTotalLinearIso_underlying :
    (SheafOfModules.toSheaf (relativeScalarSheaf J f)).mapIso
        (relativeDescendedClosedTotalLinearIso J f) = relativeDescendedClosedTotalIso J f := by
  rfl

/-- Closed total recovery preserves the original coefficient product. -/
lemma relativeDescendedClosedTotalIso_mul (U : X.Opens)
    (s t : Γ(relativeDescendedCoefficientPushforward J f, U)) :
    (relativeDescendedClosedTotalIso J f).hom.hom.app (.op U)
        (relativeDescendedMul J f U s t) =
      closedTotalCoefficientMul J f U
        ((relativeDescendedClosedTotalIso J f).hom.hom.app (.op U) s)
        ((relativeDescendedClosedTotalIso J f).hom.hom.app (.op U) t) := by
  let e := AdditiveSheafMultiplication.sectionEquiv _ _ (closedTotalSheafIso J f) (.op U)
  have h (s : Γ(relativeDescendedCoefficientPushforward J f, U)) :
      e ((relativeDescendedClosedTotalIso J f).hom.hom.app (.op U) s) =
        relativeDescendedSectionEquiv J f U s :=
    e.apply_symm_apply _
  apply e.injective
  rw [h]
  change relativeDescendedSectionEquiv J f U (relativeDescendedMul J f U s t) =
    e (AdditiveSheafMultiplication.mul _ _ (closedTotalSheafIso J f) (.op U) _ _)
  rw [AdditiveSheafMultiplication.map_mul, h, h, relativeDescendedSectionEquiv_mul]

/-- Closed total recovery preserves the original coefficient unit. -/
lemma relativeDescendedClosedTotalIso_one (U : X.Opens) :
    (relativeDescendedClosedTotalIso J f).hom.hom.app (.op U) (relativeDescendedOne J f U) =
      closedTotalCoefficientOne J f U := by
  let e := AdditiveSheafMultiplication.sectionEquiv _ _ (closedTotalSheafIso J f) (.op U)
  apply e.injective
  change e (e.symm (relativeDescendedSectionEquiv J f U (relativeDescendedOne J f U))) =
    e (AdditiveSheafMultiplication.one _ _ (closedTotalSheafIso J f) (.op U))
  rw [e.apply_symm_apply, AdditiveSheafMultiplication.map_one, relativeDescendedSectionEquiv_one]

end FLT.Mazur.IdealAdicGradedPullback
