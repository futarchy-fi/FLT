/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFamilyIso
public import FLT.Mazur.SectionPointLineCoherence

/-!
# Section-compatible original marking comparisons

The canonical section-line comparison under arbitrary base change preserves
the vanishing section. Its tensor powers are the existing pole comparisons.
The same statements hold for the inverse of a full family isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPointLineIso
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (g : T ⟶ S)
  (s : 𝟙_ (Over S) ⟶ E.group)
local instance markingLineCoherenceProper : IsProper E.curve.hom := E.family.family.1
local notation "t" => s ≫ E.inclusion
local notation "v" => pullSection g s ≫ GeneralizedEllipticCurve.inclusion (E.baseChange g)
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
local notation "hJ" => And.left (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s))

/-- The original section-line comparison, before taking any tensor power. -/
def smoothMarkingPointLineBaseChangeIso :
    (pullback (Limits.pullback.fst E.curve.hom g)).obj (divisorLineBundle (t).left.ker hI) ≅
      divisorLineBundle (v).left.ker hJ :=
  sectionPointLineIso (IsPullback.of_hasPullback E.curve.hom g)
    (t).left (v).left (t).w (v).w
    (by rw [← pullSection_smoothMarking]; exact section_fst g (t)) hI hJ

/-- Arbitrary base change preserves the canonical vanishing section of the marking. -/
theorem smoothMarkingPointLineBaseChangeIso_compatible :
    DivisorLineSectionCompatible (Limits.pullback.fst E.curve.hom g) hI hJ
      (smoothMarkingPointLineBaseChangeIso E g s) := by
  unfold smoothMarkingPointLineBaseChangeIso
  exact sectionPointLineIso_compatible (IsPullback.of_hasPullback E.curve.hom g)
    (t).left (v).left (t).w (v).w
    (by rw [← pullSection_smoothMarking]; exact section_fst g (t)) hI hJ

/-- The original pole comparison is the power of the section-line comparison. -/
theorem smoothMarkingPowerBaseChangeIso_eq (m : ℕ) :
    E.smoothMarkingPowerBaseChangeIso g s m =
      tensorPowerPullbackComparison (Limits.pullback.fst E.curve.hom g)
        (smoothMarkingPointLineBaseChangeIso E g s) m := rfl

variable {E} {F : GeneralizedEllipticCurve S} (e : E ≅ F)

/-- The sealed family-isomorphism line comparison preserves the vanishing section. -/
theorem smoothMarkingFamilyLineIso_compatible :
    DivisorLineSectionCompatible e.inv.curve.left hI
      (smoothMarking_relativeCartier F (s ≫ e.hom.group)).1
      (smoothMarkingFamilyLineIso e s) := by
  rw [smoothMarkingFamilyLineIso_def]
  exact sectionPointLineIso_compatible (smoothMarkingIso_cartesian e)
    (t).left ((s ≫ e.hom.group) ≫ F.inclusion).left (t).w
    ((s ≫ e.hom.group) ≫ F.inclusion).w (smoothMarkingIso_sectionSquare e s) hI _

/-- The family pole comparison is the power of the same canonical line comparison. -/
theorem smoothMarkingFamilyPowerIso_eq (m : ℕ) :
    smoothMarkingFamilyPowerIso e s m =
      tensorPowerPullbackComparison e.inv.curve.left (smoothMarkingFamilyLineIso e s) m := by
  rw [smoothMarkingFamilyLineIso_def]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
