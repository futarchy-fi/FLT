/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdditiveSheafModuleTransport
public import FLT.Mazur.IdealAdicRelativeDescendedMultiplication
public import FLT.Mazur.IdealAdicRelativeAffineSheaf

/-!
# The global relative action on descended pushforward sections

The original relative coefficient action gives a module sheaf on the
actual additive pushforward. Its recovery is linear globally, and on every
affine open the scalar action is the original relative tensor action.
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
attribute [local irreducible] relativePushforwardCoefficientSectionsIso
attribute [local irreducible] relativeDescendedCoefficientPushforward

/-- The relative module structure on the actual additive pushforward. -/
def relativeDescendedRelativeModule : SheafOfModules (relativeScalarSheaf J f) :=
  AdditiveSheafModuleTransport.moduleSheaf _ (relativeCoefficientModuleSheaf J f)
    (relativeDescendedCoefficientUnderlyingIso J f)

/-- This relative module has exactly the actual descended pushforward as additive sheaf. -/
lemma relativeDescendedRelativeModule_underlying :
    (SheafOfModules.toSheaf (relativeScalarSheaf J f)).obj
        (relativeDescendedRelativeModule J f) =
      (SheafOfModules.toSheaf X.ringCatSheaf).obj
        (relativeDescendedCoefficientPushforward J f) := rfl

/-- Recovery is an isomorphism for the global relative scalar action. -/
def relativeDescendedRelativeModuleIso :
    relativeDescendedRelativeModule J f ≅ relativeCoefficientModuleSheaf J f :=
  AdditiveSheafModuleTransport.moduleIso _ (relativeCoefficientModuleSheaf J f)
    (relativeDescendedCoefficientUnderlyingIso J f)

/-- The linear recovery retains the original global additive comparison. -/
lemma relativeDescendedRelativeModuleIso_underlying :
    (SheafOfModules.toSheaf (relativeScalarSheaf J f)).map
        (relativeDescendedRelativeModuleIso J f).hom =
      (relativeDescendedCoefficientUnderlyingIso J f).hom := rfl

/-- The relative scalar action on unchanged descended pushforward sections. -/
def relativeDescendedRelativeSmul (U : X.Opens)
    (r : (relativeRingSheaf J f).obj.obj (.op U))
    (s : Γ(relativeDescendedCoefficientPushforward J f, U)) :
    Γ(relativeDescendedCoefficientPushforward J f, U) :=
  (show (relativeDescendedRelativeModule J f).val.obj (.op U) from
    r • (show (relativeDescendedRelativeModule J f).val.obj (.op U) from s))

/-- Global recovery retains multiplication by the actual relative quotient. -/
lemma relativeDescendedSectionEquiv_smul (U : X.Opens)
    (r : (relativeRingSheaf J f).obj.obj (.op U))
    (s : Γ(relativeDescendedCoefficientPushforward J f, U)) :
    relativeDescendedSectionEquiv J f U (relativeDescendedRelativeSmul J f U r s) =
      (relativeSheafQuotient J f).hom.app (.op U) r * relativeDescendedSectionEquiv J f U s :=
  AdditiveSheafModuleTransport.map_smul _ (relativeCoefficientModuleSheaf J f)
    (relativeDescendedCoefficientUnderlyingIso J f) (.op U) r s

/-- The action commutes with the actual descended pushforward restrictions. -/
lemma relativeDescendedRelativeSmul_restrict {U V : X.Opens} (i : U ⟶ V)
    (r : (relativeRingSheaf J f).obj.obj (.op V))
    (s : Γ(relativeDescendedCoefficientPushforward J f, V)) :
    (relativeDescendedCoefficientPushforward J f).presheaf.map i.op
        (relativeDescendedRelativeSmul J f V r s) =
      relativeDescendedRelativeSmul J f U ((relativeRingSheaf J f).obj.map i.op r)
        ((relativeDescendedCoefficientPushforward J f).presheaf.map i.op s) :=
  AdditiveSheafModuleTransport.restrict_smul _ (relativeCoefficientModuleSheaf J f)
    (relativeDescendedCoefficientUnderlyingIso J f) i.op r s

/-- Affine recovery gives multiplication by the original relative algebra quotient. -/
lemma relativePushforwardCoefficientSectionsIso_smul (U : X.affineOpens)
    (r : RelativeAlgebra J f U)
    (s : Γ(relativeDescendedCoefficientPushforward J f, U.1)) :
    let := closedBaseAlgebra J f U.1
    let := localBaseAlgebra J f U.1
    (relativePushforwardCoefficientSectionsIso J f U).hom
        (relativeDescendedRelativeSmul J f U.1 ((relativeChartIso J f U).hom r) s) =
      relativeMap J f U r * (relativePushforwardCoefficientSectionsIso J f U).hom s := by
  intro _ _
  apply (ConcreteCategory.bijective_of_isIso (coefficientChartIso J f U).hom).injective
  rw [← relativeDescendedSectionEquiv_affine, relativeDescendedSectionEquiv_smul, map_mul]
  rw [relativeDescendedSectionEquiv_affine]
  congr 1
  exact ConcreteCategory.congr_hom (relativeChartIso_quotient J f U) r

/-- Affine recovery is linear for the original tensor coefficient module structure. -/
lemma relativePushforwardCoefficientSectionsIso_relativeAction (U : X.affineOpens)
    (r : RelativeAlgebra J f U)
    (s : Γ(relativeDescendedCoefficientPushforward J f, U.1)) :
    let := closedBaseAlgebra J f U.1
    (relativePushforwardCoefficientSectionsIso J f U).hom
        (relativeDescendedRelativeSmul J f U.1 ((relativeChartIso J f U).hom r) s) =
      r • (show relativeChartCoefficient J f U from
        (relativePushforwardCoefficientSectionsIso J f U).hom s) :=
  relativePushforwardCoefficientSectionsIso_smul J f U r s

end FLT.Mazur.IdealAdicGradedPullback
