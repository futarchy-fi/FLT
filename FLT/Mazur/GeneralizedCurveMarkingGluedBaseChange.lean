/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingGluedSection

/-!
# The pointed cubic over arbitrary test bases

The constructed cubic and the actual whole-family map pull back along any
map to the original locally Noetherian base. The test base is unrestricted;
the pulled-back infinity section is still the image of its original marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (g : T ⟶ S)

/-- The actual cubic on an arbitrary test base is a categorical base change. -/
def smoothMarkingPulledCubic : Scheme := Limits.pullback (smoothMarkingGluedBase E s) g

/-- The original cubic projection from the arbitrary test. -/
def smoothMarkingPulledProjection : smoothMarkingPulledCubic E s g ⟶
    smoothMarkingGluedCubic E s := Limits.pullback.fst _ _

/-- The structure map over the actual test base. -/
def smoothMarkingPulledBase : smoothMarkingPulledCubic E s g ⟶ T :=
  Limits.pullback.snd _ _

/-- The arbitrary test cubic retains the original base square. -/
theorem smoothMarkingPulled_isPullback :
    IsPullback (smoothMarkingPulledProjection E s g) (smoothMarkingPulledBase E s g)
      (smoothMarkingGluedBase E s) g := IsPullback.of_hasPullback _ _

/-- The whole original pulled-back family maps to the categorical pulled-back cubic. -/
def smoothMarkingToPulledCubic : (E.baseChange g).curve.left ⟶
    smoothMarkingPulledCubic E s g :=
  Limits.pullback.lift
    (Limits.pullback.fst E.curve.hom g ≫ smoothMarkingToGluedCubic E s)
    (Limits.pullback.snd E.curve.hom g)
    (by rw [Category.assoc, smoothMarkingToGluedCubic_over]; exact Limits.pullback.condition)

/-- Projection recovers the actual global whole-curve map. -/
@[reassoc] theorem smoothMarkingToPulledCubic_projection :
    smoothMarkingToPulledCubic E s g ≫ smoothMarkingPulledProjection E s g =
      Limits.pullback.fst E.curve.hom g ≫ smoothMarkingToGluedCubic E s :=
  Limits.pullback.lift_fst _ _ _

/-- The test map retains the whole original family's structure morphism. -/
@[reassoc] theorem smoothMarkingToPulledCubic_over :
    smoothMarkingToPulledCubic E s g ≫ smoothMarkingPulledBase E s g =
      (E.baseChange g).curve.hom := Limits.pullback.lift_snd _ _ _

/-- The infinity section on the arbitrary test, constructed by the pullback property. -/
def smoothMarkingPulledZero : T ⟶ smoothMarkingPulledCubic E s g :=
  Limits.pullback.lift (g ≫ smoothMarkingGluedZero E s) (𝟙 T)
    (by rw [Category.assoc, smoothMarkingGluedZero_over,
      Category.comp_id, Category.id_comp])

/-- The infinity section retains its original image. -/
@[reassoc] theorem smoothMarkingPulledZero_projection :
    smoothMarkingPulledZero E s g ≫ smoothMarkingPulledProjection E s g =
      g ≫ smoothMarkingGluedZero E s := Limits.pullback.lift_fst _ _ _

/-- The pulled-back infinity is a section over the actual test base. -/
@[reassoc] theorem smoothMarkingPulledZero_over :
    smoothMarkingPulledZero E s g ≫ smoothMarkingPulledBase E s g = 𝟙 T :=
  Limits.pullback.lift_snd _ _ _

/-- The original marking on the test family maps to the constructed infinity section. -/
@[reassoc] theorem smoothMarkingToPulledCubic_marking :
    (pullSection g s ≫ (E.baseChange g).inclusion).left ≫
      smoothMarkingToPulledCubic E s g = smoothMarkingPulledZero E s g := by
  apply Limits.pullback.hom_ext
  · change _ ≫ smoothMarkingPulledProjection E s g =
      smoothMarkingPulledZero E s g ≫ smoothMarkingPulledProjection E s g
    rw [Category.assoc, smoothMarkingToPulledCubic_projection,
      ← pullSection_smoothMarking, ← Category.assoc, section_fst,
      Category.assoc, smoothMarkingPulledZero_projection]
    rfl
  · change _ ≫ smoothMarkingPulledBase E s g =
      smoothMarkingPulledZero E s g ≫ smoothMarkingPulledBase E s g
    rw [Category.assoc, smoothMarkingToPulledCubic_over, smoothMarkingPulledZero_over]
    exact (pullSection g s ≫ (E.baseChange g).inclusion).w

/-- Properness of the constructed cubic survives arbitrary test schemes. -/
instance smoothMarkingPulledBase_isProper : IsProper (smoothMarkingPulledBase E s g) := by
  unfold smoothMarkingPulledBase
  infer_instance

/-- Infinity stays a closed section on every arbitrary test. -/
instance smoothMarkingPulledZero_isClosedImmersion :
    IsClosedImmersion (smoothMarkingPulledZero E s g) := by
  have : IsClosedImmersion (smoothMarkingPulledZero E s g ≫ smoothMarkingPulledBase E s g) := by
    rw [smoothMarkingPulledZero_over]
    infer_instance
  exact IsClosedImmersion.of_comp (smoothMarkingPulledZero E s g)
    (smoothMarkingPulledBase E s g)

end FLT.Mazur.GeneralizedEllipticCurve
