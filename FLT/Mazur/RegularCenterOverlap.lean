/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterRatioCover
public import FLT.Mazur.BlowupReesRatioTransition

/-!
# Actual transitions on overlaps of principalized-center ratio opens

If two generator quotients are units, both original output fraction charts
receive maps from the input. Their maps factor through the entire original
ratio intersection and agree through its canonical transition. The retained
principal denominator is only required to be regular, never a unit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.RegularCenter

open BlowupFractionChart BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048

variable {A B : Type*} [CommRing A] [CommRing B]
  (I : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (hd : IsRegular d) (a : A) (ha : a ∈ I)
  (hu : IsUnit (quotient I φ d hI a ha))

include hu in
/-- An invertible generator quotient makes that actual generator span the pulled-back center. -/
theorem unitQuotient_center : I.map φ = Ideal.span {φ a} := by
  rw [← denominator_mul_quotient I φ d hI a ha,
    Ideal.span_singleton_mul_right_unit hu, hI]

include hd hu in
/-- The original output denominator is regular wherever its input quotient is invertible. -/
theorem unitQuotient_regular : IsRegular (φ a) := by
  rw [← denominator_mul_quotient I φ d hI a ha]
  exact hd.mul hu.isRegular

/-- The actual fraction-chart map on any domain where the generator quotient is a unit. -/
irreducible_def unitQuotientLift : chart I a →+* B :=
  principalLift I φ a (unitQuotient_center I φ d hI a ha hu).le
    (unitQuotient_regular I φ d hI hd a ha hu)

/-- The map on a unit quotient domain retains every original coefficient. -/
@[simp] theorem unitQuotientLift_base (z : A) :
    unitQuotientLift I φ d hI hd a ha hu (algebraMap A _ z) = φ z := by
  rw [unitQuotientLift_def, principalLift_base]

/-- The image of an original target ratio is the corresponding quotient of input ratios. -/
theorem quotient_mul_unitQuotientLift_ratio (b : A) (hb : b ∈ I) :
    quotient I φ d hI a ha * unitQuotientLift I φ d hI hd a ha hu (ratio I a b hb) =
      quotient I φ d hI b hb := by
  apply hd.left
  dsimp only
  rw [← mul_assoc, denominator_mul_quotient, denominator_mul_quotient]
  rw [unitQuotientLift_def]
  exact principalLift_ratio I φ a _ _ b hb

/-- Both unit input quotients make the actual output transition ratio invertible. -/
theorem unitQuotientLift_ratio_isUnit (b : A) (hb : b ∈ I)
    (hv : IsUnit (quotient I φ d hI b hb)) :
    IsUnit (unitQuotientLift I φ d hI hd a ha hu (ratio I a b hb)) := by
  have h : IsUnit (quotient I φ d hI a ha *
      unitQuotientLift I φ d hI hd a ha hu (ratio I a b hb)) := by
    rw [quotient_mul_unitQuotientLift_ratio]
    exact hv
  exact isUnit_of_mul_isUnit_right h

/-- The map into the whole target ratio intersection, including its exceptional points. -/
irreducible_def unitRatioLift (b : A) (hb : b ∈ I)
    (hv : IsUnit (quotient I φ d hI b hb)) : FractionRatioOpen I a b hb →+* B :=
  IsLocalization.Away.lift (ratio I a b hb)
    (unitQuotientLift_ratio_isUnit I φ d hI hd a ha hu b hb hv)

/-- The intersection map extends the complete original target fraction-chart map. -/
@[simp] theorem unitRatioLift_chart (b : A) (hb : b ∈ I)
    (hv : IsUnit (quotient I φ d hI b hb)) (z : chart I a) :
    unitRatioLift I φ d hI hd a ha hu b hb hv (algebraMap _ _ z) =
      unitQuotientLift I φ d hI hd a ha hu z := by
  rw [unitRatioLift_def, IsLocalization.Away.lift_eq]

/-- Every original coefficient is preserved on the full target ratio intersection. -/
@[simp] theorem unitRatioLift_original (b : A) (hb : b ∈ I)
    (hv : IsUnit (quotient I φ d hI b hb)) (z : A) :
    unitRatioLift I φ d hI hd a ha hu b hb hv (originalOnRatio I a b hb z) = φ z := by
  rw [originalOnRatio, RingHom.comp_apply, unitRatioLift_chart, unitQuotientLift_base]

/-- The two chart maps agree through the canonical original Rees transition. -/
theorem unitRatioLift_transition (b : A) (hb : b ∈ I)
    (hv : IsUnit (quotient I φ d hI b hb)) :
    (unitRatioLift I φ d hI hd a ha hu b hb hv).comp
        (ratioTransition I b hb a ha).toRingHom =
      unitRatioLift I φ d hI hd b hb hv a ha hu := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (ratio I b a ha))
  apply ringHom_ext_of_denominator_regular I b
  · ext z
    change unitRatioLift I φ d hI hd a ha hu b hb hv
      (ratioTransition I b hb a ha (originalOnRatio I b a ha z)) =
        unitRatioLift I φ d hI hd b hb hv a ha hu (originalOnRatio I b a ha z)
    rw [ratioTransition_original, unitRatioLift_original, unitRatioLift_original]
  · change IsRegular (unitRatioLift I φ d hI hd a ha hu b hb hv
      (ratioTransition I b hb a ha (originalOnRatio I b a ha b)))
    rw [ratioTransition_original, unitRatioLift_original]
    exact unitQuotient_regular I φ d hI hd b hb hv

end FLT.Mazur.RegularCenter
