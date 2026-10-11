/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterOverlapScheme

/-!
# Restricting the actual quotient-open lifts

Quotients by a regular denominator commute with restriction whenever the
denominator remains regular. Consequently the constructed quotient-open lifts
agree after restriction to any common domain on which both quotients are units.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.RegularCenter

open BlowupFractionChart BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
  (I : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (ψ : B →+* T)

include hI in
/-- Restriction retains the entire principalized center. -/
theorem mapped_center : I.map (ψ.comp φ) = Ideal.span {ψ d} := by
  rw [← Ideal.map_map, hI, Ideal.map_span, Set.image_singleton]

/-- Actual quotients commute with every restriction preserving denominator regularity. -/
theorem mapped_quotient (hdT : IsRegular (ψ d)) (a : A) (ha : a ∈ I) :
    ψ (quotient I φ d hI a ha) =
      quotient I (ψ.comp φ) (ψ d) (mapped_center I φ d hI ψ) a ha := by
  apply quotient_unique _ _ _ _ hdT
  rw [← map_mul, denominator_mul_quotient]
  rfl

/-- An invertible restricted quotient is the actual quotient on the restricted domain. -/
theorem mapped_quotient_isUnit (hdT : IsRegular (ψ d)) (a : A) (ha : a ∈ I)
    (hu : IsUnit (ψ (quotient I φ d hI a ha))) :
    IsUnit (quotient I (ψ.comp φ) (ψ d) (mapped_center I φ d hI ψ) a ha) := by
  rwa [← mapped_quotient I φ d hI ψ hdT]

/-- The map from an actual quotient localization to a common restriction domain. -/
def quotientRestriction (a : A) (ha : a ∈ I)
    (hu : IsUnit (ψ (quotient I φ d hI a ha))) : QuotientOpen I φ d hI a ha →+* T :=
  IsLocalization.Away.lift (quotient I φ d hI a ha) hu

/-- The localization restriction keeps every original input function. -/
@[simp] theorem quotientRestriction_base (a : A) (ha : a ∈ I)
    (hu : IsUnit (ψ (quotient I φ d hI a ha))) (z : B) :
    quotientRestriction I φ d hI ψ a ha hu (algebraMap B _ z) = ψ z :=
  IsLocalization.Away.lift_eq _ _ _

/-- Restricting a constructed chart lift gives the original-preserving unit-quotient lift. -/
theorem quotientOpenLift_restrict (hd : IsRegular d) (hdT : IsRegular (ψ d))
    (a : A) (ha : a ∈ I) (hu : IsUnit (ψ (quotient I φ d hI a ha))) :
    (quotientRestriction I φ d hI ψ a ha hu).comp (quotientOpenLift I φ d hI a ha hd) =
      unitQuotientLift I (ψ.comp φ) (ψ d) (mapped_center I φ d hI ψ) hdT a ha
        (mapped_quotient_isUnit I φ d hI ψ hdT a ha hu) := by
  apply ringHom_ext_of_denominator_regular I a
  · ext z
    change quotientRestriction I φ d hI ψ a ha hu
      (quotientOpenLift I φ d hI a ha hd (algebraMap A _ z)) = _
    rw [quotientOpenLift_base, RingHom.comp_apply, unitQuotientLift_base]
    exact quotientRestriction_base I φ d hI ψ a ha hu (φ z)
  · change IsRegular (quotientRestriction I φ d hI ψ a ha hu
      (quotientOpenLift I φ d hI a ha hd (algebraMap A _ a)))
    rw [quotientOpenLift_base]
    change IsRegular (quotientRestriction I φ d hI ψ a ha hu (algebraMap B _ (φ a)))
    rw [quotientRestriction_base]
    exact unitQuotient_regular I (ψ.comp φ) (ψ d) (mapped_center I φ d hI ψ) hdT a ha
      (mapped_quotient_isUnit I φ d hI ψ hdT a ha hu)

/-- The actual quotient-open chart lift viewed as a morphism into the original Rees Proj. -/
def quotientOpenToProj (hd : IsRegular d) (a : A) (ha : a ∈ I) :
    Spec (.of (QuotientOpen I φ d hI a ha)) ⟶ proj I :=
  Spec.map (CommRingCat.ofHom (quotientOpenLift I φ d hI a ha hd)) ≫
    fractionChartInclusion I a ha

/-- Restriction into the original Proj agrees with the canonical unit-quotient presentation. -/
theorem quotientOpenToProj_restrict (hd : IsRegular d) (hdT : IsRegular (ψ d))
    (a : A) (ha : a ∈ I) (hu : IsUnit (ψ (quotient I φ d hI a ha))) :
    Spec.map (CommRingCat.ofHom (quotientRestriction I φ d hI ψ a ha hu)) ≫
        quotientOpenToProj I φ d hI hd a ha =
      unitQuotientToProj I (ψ.comp φ) (ψ d) (mapped_center I φ d hI ψ) hdT a ha
        (mapped_quotient_isUnit I φ d hI ψ hdT a ha hu) := by
  rw [quotientOpenToProj, unitQuotientToProj, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (quotientOpenLift_restrict I φ d hI ψ hd hdT a ha hu)

end FLT.Mazur.RegularCenter
