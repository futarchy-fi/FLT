/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingGluedBaseChange
public import FLT.Mazur.SectionCartesianKernel

/-!
# Whole-curve and infinity pullback squares on unrestricted tests

The actual test-family map is a categorical pullback of the original map.
The infinity square is cartesian too, retaining its full ideal rather than
only its support. No Noetherian assumption is placed on the test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (g : T ⟶ S)

/-- The actual whole-curve map on any test is the categorical pullback of the original map. -/
theorem smoothMarkingToPulledCubic_isPullback :
    IsPullback (smoothMarkingToPulledCubic E s g) (Limits.pullback.fst E.curve.hom g)
      (smoothMarkingPulledProjection E s g) (smoothMarkingToGluedCubic E s) := by
  have h : IsPullback
      (smoothMarkingToPulledCubic E s g ≫ smoothMarkingPulledBase E s g)
      (Limits.pullback.fst E.curve.hom g) g
      (smoothMarkingToGluedCubic E s ≫ smoothMarkingGluedBase E s) := by
    rw [smoothMarkingToPulledCubic_over, smoothMarkingToGluedCubic_over]
    exact (IsPullback.of_hasPullback E.curve.hom g).flip
  exact h.of_right (smoothMarkingToPulledCubic_projection E s g)
    (smoothMarkingPulled_isPullback E s g).flip

/-- The entire original test family still maps properly to the constructed test cubic. -/
instance smoothMarkingToPulledCubic_isProper : IsProper (smoothMarkingToPulledCubic E s g) :=
  MorphismProperty.of_isPullback (smoothMarkingToPulledCubic_isPullback E s g).flip
    (smoothMarkingToGluedCubic_isProper E s)

/-- The actual infinity section is cartesian on every test, including nonflat tests. -/
theorem smoothMarkingPulledZero_isPullback :
    IsPullback (smoothMarkingPulledZero E s g) g
      (smoothMarkingPulledProjection E s g) (smoothMarkingGluedZero E s) :=
  FCurve.section_isPullback_of_cartesian (smoothMarkingPulled_isPullback E s g)
    (smoothMarkingPulledZero E s g) (smoothMarkingGluedZero E s)
    (smoothMarkingPulledZero_over E s g) (smoothMarkingGluedZero_over E s)
    (smoothMarkingPulledZero_projection E s g)

/-- The infinity ideal, including nilpotents, is the pullback of the original infinity ideal. -/
theorem smoothMarkingPulledZero_ker :
    (smoothMarkingGluedZero E s).ker.comap (smoothMarkingPulledProjection E s g) =
      (smoothMarkingPulledZero E s g).ker :=
  FCurve.section_ker_comap_of_cartesian (smoothMarkingPulled_isPullback E s g)
    (smoothMarkingPulledZero E s g) (smoothMarkingGluedZero E s)
    (smoothMarkingPulledZero_over E s g) (smoothMarkingGluedZero_over E s)
    (smoothMarkingPulledZero_projection E s g)

end FLT.Mazur.GeneralizedEllipticCurve
