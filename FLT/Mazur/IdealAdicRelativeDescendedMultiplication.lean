/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdditiveSheafMultiplication
public import FLT.Mazur.IdealAdicRelativeDescendedUnderlying

/-!
# Original multiplication on the actual descended pushforward

Transport the global coefficient product to the actual pushforward sections.
The affine recovery identifies this product with the original graded
coefficient multiplication, including its unit and restriction maps.
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

/-- The global additive recovery as an equivalence with ring-valued sections. -/
def relativeDescendedSectionEquiv (U : X.Opens) :
    Γ(relativeDescendedCoefficientPushforward J f, U) ≃+
      (coefficientRingSheaf J f).obj.obj (.op U) :=
  AdditiveSheafMultiplication.sectionEquiv _ _
    (relativeDescendedCoefficientUnderlyingIso J f) (.op U)

/-- On an affine open, global recovery is the canonical chart recovery. -/
lemma relativeDescendedSectionEquiv_affine (U : X.affineOpens)
    (s : Γ(relativeDescendedCoefficientPushforward J f, U.1)) :
    relativeDescendedSectionEquiv J f U.1 s =
      (coefficientChartIso J f U).hom
        ((relativePushforwardCoefficientSectionsIso J f U).hom s) := by
  have h := congrArg (fun k ↦ k.hom.app (.op U))
    (relativeDescendedCoefficientUnderlyingIso_basis J f)
  exact ConcreteCategory.congr_hom h s

/-- The global coefficient multiplication on the actual descended pushforward sections. -/
def relativeDescendedMul (U : X.Opens)
    (s t : Γ(relativeDescendedCoefficientPushforward J f, U)) :
    Γ(relativeDescendedCoefficientPushforward J f, U) :=
  AdditiveSheafMultiplication.mul _ _ (relativeDescendedCoefficientUnderlyingIso J f) (.op U) s t

/-- The original coefficient unit on the actual descended pushforward sections. -/
def relativeDescendedOne (U : X.Opens) :
    Γ(relativeDescendedCoefficientPushforward J f, U) :=
  AdditiveSheafMultiplication.one _ _ (relativeDescendedCoefficientUnderlyingIso J f) (.op U)

/-- Recovery preserves the global coefficient product. -/
lemma relativeDescendedSectionEquiv_mul (U : X.Opens)
    (s t : Γ(relativeDescendedCoefficientPushforward J f, U)) :
    relativeDescendedSectionEquiv J f U (relativeDescendedMul J f U s t) =
      relativeDescendedSectionEquiv J f U s * relativeDescendedSectionEquiv J f U t :=
  AdditiveSheafMultiplication.map_mul _ _
    (relativeDescendedCoefficientUnderlyingIso J f) (.op U) s t

/-- Recovery preserves the coefficient unit. -/
lemma relativeDescendedSectionEquiv_one (U : X.Opens) :
    relativeDescendedSectionEquiv J f U (relativeDescendedOne J f U) = 1 :=
  AdditiveSheafMultiplication.map_one _ _
    (relativeDescendedCoefficientUnderlyingIso J f) (.op U)

/-- Affine recovery retains the original coefficient multiplication. -/
lemma relativePushforwardCoefficientSectionsIso_mul (U : X.affineOpens)
    (s t : Γ(relativeDescendedCoefficientPushforward J f, U.1)) :
    (relativePushforwardCoefficientSectionsIso J f U).hom (relativeDescendedMul J f U.1 s t) =
      (show IdealAdicGradedSections.Sections (J.comap f) U.1 from
        (relativePushforwardCoefficientSectionsIso J f U).hom s) *
        (relativePushforwardCoefficientSectionsIso J f U).hom t := by
  apply (ConcreteCategory.bijective_of_isIso (coefficientChartIso J f U).hom).injective
  rw [map_mul, ← relativeDescendedSectionEquiv_affine, ← relativeDescendedSectionEquiv_affine,
    ← relativeDescendedSectionEquiv_affine, relativeDescendedSectionEquiv_mul]

/-- Affine recovery retains the original coefficient unit. -/
lemma relativePushforwardCoefficientSectionsIso_one (U : X.affineOpens) :
    (relativePushforwardCoefficientSectionsIso J f U).hom (relativeDescendedOne J f U.1) =
      (1 : IdealAdicGradedSections.Sections (J.comap f) U.1) := by
  apply (ConcreteCategory.bijective_of_isIso (coefficientChartIso J f U).hom).injective
  rw [map_one, ← relativeDescendedSectionEquiv_affine, relativeDescendedSectionEquiv_one]

/-- The actual restriction maps preserve coefficient multiplication. -/
lemma relativeDescendedMul_restrict {U V : X.Opens} (i : U ⟶ V)
    (s t : Γ(relativeDescendedCoefficientPushforward J f, V)) :
    (relativeDescendedCoefficientPushforward J f).presheaf.map i.op
        (relativeDescendedMul J f V s t) =
      relativeDescendedMul J f U
        ((relativeDescendedCoefficientPushforward J f).presheaf.map i.op s)
        ((relativeDescendedCoefficientPushforward J f).presheaf.map i.op t) :=
  AdditiveSheafMultiplication.restrict_mul _ _
    (relativeDescendedCoefficientUnderlyingIso J f) i.op s t

/-- The actual restriction maps preserve the original unit. -/
lemma relativeDescendedOne_restrict {U V : X.Opens} (i : U ⟶ V) :
    (relativeDescendedCoefficientPushforward J f).presheaf.map i.op
      (relativeDescendedOne J f V) = relativeDescendedOne J f U :=
  AdditiveSheafMultiplication.restrict_one _ _
    (relativeDescendedCoefficientUnderlyingIso J f) i.op

end FLT.Mazur.IdealAdicGradedPullback
