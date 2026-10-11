/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterOverlap

/-!
# Scheme compatibility of the actual fraction lifts

On every domain where two original generator quotients are units, the two
constructed lifts give exactly the same morphism into the original Rees Proj.
The equality factors through the full canonical Rees intersection.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.RegularCenter

open BlowupFractionChart BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (I : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (hd : IsRegular d) (a : A) (ha : a ∈ I)
  (hu : IsUnit (quotient I φ d hI a ha))

/-- The actual map into original Rees Proj through a generator fraction chart. -/
def unitQuotientToProj : Spec (.of B) ⟶ proj I :=
  Spec.map (CommRingCat.ofHom (unitQuotientLift I φ d hI hd a ha hu)) ≫
    fractionChartInclusion I a ha

/-- The target intersection map retains the original entire fraction-chart lift. -/
@[reassoc] theorem unitRatioLift_spec_chart (b : A) (hb : b ∈ I)
    (hv : IsUnit (quotient I φ d hI b hb)) :
    Spec.map (CommRingCat.ofHom (R := FractionRatioOpen I a b hb) (S := B)
      (unitRatioLift I φ d hI hd a ha hu b hb hv)) ≫
        fractionRatioInclusion I a b hb =
      Spec.map (CommRingCat.ofHom (unitQuotientLift I φ d hI hd a ha hu)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z
  exact unitRatioLift_chart I φ d hI hd a ha hu b hb hv z

/-- Scheme maps through the two original intersections commute via the canonical transition. -/
@[reassoc] theorem unitRatioLift_spec_transition (b : A) (hb : b ∈ I)
    (hv : IsUnit (quotient I φ d hI b hb)) :
    Spec.map (CommRingCat.ofHom (R := FractionRatioOpen I a b hb) (S := B)
      (unitRatioLift I φ d hI hd a ha hu b hb hv)) ≫
        Spec.map (CommRingCat.ofHom (R := FractionRatioOpen I b a ha)
          (S := FractionRatioOpen I a b hb) (ratioTransition I b hb a ha).toRingHom) =
      Spec.map (CommRingCat.ofHom (R := FractionRatioOpen I b a ha) (S := B)
        (unitRatioLift I φ d hI hd b hb hv a ha hu)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact unitRatioLift_transition I φ d hI hd a ha hu b hb hv

/-- The actual local action lifts agree in the original Rees Proj on every ratio overlap. -/
theorem unitQuotientToProj_eq (b : A) (hb : b ∈ I)
    (hv : IsUnit (quotient I φ d hI b hb)) :
    unitQuotientToProj I φ d hI hd a ha hu = unitQuotientToProj I φ d hI hd b hb hv := by
  unfold unitQuotientToProj
  rw [← unitRatioLift_spec_chart I φ d hI hd a ha hu b hb hv,
    Category.assoc, ← ratioTransition_inclusion I b hb a ha,
    unitRatioLift_spec_transition_assoc, unitRatioLift_spec_chart_assoc]

end FLT.Mazur.RegularCenter
