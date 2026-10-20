/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationNegationBoundary
public import FLT.Mazur.WeierstrassSuccessiveNegation
public import FLT.Mazur.WeierstrassSuccessiveXHorizontalScheme

/-!
# The successor negative retains the entire preceding exterior boundary

Localize at the fixed preceding horizontal coordinate. The proved contraction
comparison identifies this involution with the original divided boundary
negative, including every regular function on the retained principal open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "f" => negation W s π b3 b4 b6
local notation "u" => coord W s π b3 b4 b6 2
local notation "H" => horizontalIso W s π b3 b4 b6
local notation "P" => WeierstrassDilatation.horizontalNegationIso W s
  (π * b3) (π * b4) (π ^ 2 * b6)

/-- Negation of the entire retained-horizontal principal open of the incidence chart. -/
def horizontalNegationIso : Spec (.of (HorizontalOpen W s π b3 b4 b6)) ≅
    Spec (.of (HorizontalOpen W s π b3 b4 b6)) :=
  LocalizationFixedInvolution.specIso f u (negation_u W s π b3 b4 b6)
    (negation_comp W s π b3 b4 b6)

/-- The retained-horizontal involution preserves its original incidence-chart inclusion. -/
@[reassoc] theorem horizontalNegationIso_inclusion :
    (horizontalNegationIso W s π b3 b4 b6).hom ≫
        horizontalOpenInclusion W s π b3 b4 b6 =
      horizontalOpenInclusion W s π b3 b4 b6 ≫ (negationIso W s π b3 b4 b6).hom :=
  LocalizationFixedInvolution.specIso_inclusion f u (negation_u W s π b3 b4 b6)
    (negation_comp W s π b3 b4 b6)

/-- The actual horizontal comparison identifies the two constructed boundary negatives. -/
@[reassoc] theorem horizontalNegationIso_comparison :
    (horizontalNegationIso W s π b3 b4 b6).hom ≫ (H).hom = (H).hom ≫ (P).hom := by
  apply (cancel_mono (previousHorizontalInclusion W s π b3 b4 b6)).mp
  simp only [Category.assoc, horizontalIso_toDivided]
  change _ = (H).hom ≫ (P).hom ≫
    WeierstrassDilatation.horizontalInclusion W s (π * b3) (π * b4) (π ^ 2 * b6)
  rw [WeierstrassDilatation.horizontalNegationIso_inclusion,
    horizontalNegationIso_inclusion_assoc, negationIso_toDivided]
  exact (horizontalIso_toDivided_assoc W s π b3 b4 b6 _).symm

/-- The full preceding horizontal boundary is invariant in the actual local successor. -/
@[reassoc] theorem previousHorizontalChart_negation :
    (P).hom ≫ previousHorizontalChart W s π b3 b4 b6 =
      previousHorizontalChart W s π b3 b4 b6 ≫
        modificationNegation W s π b3 b4 b6 := by
  apply (cancel_epi (H).hom).mp
  rw [← horizontalNegationIso_comparison_assoc]
  simp only [previousHorizontalChart, Category.assoc, Iso.hom_inv_id_assoc]
  rw [horizontalNegationIso_inclusion_assoc, xChart_modificationNegation]

end FLT.Mazur.WeierstrassSuccessiveX
