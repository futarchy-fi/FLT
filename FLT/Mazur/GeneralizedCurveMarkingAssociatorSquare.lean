/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAssociatorLine

/-!
# Direct and successive pullbacks of the original marking

The inverse family associator and the two base projections give a commuting
square of the actual marking lines. Every original pole power obeys the same
square, including degree zero and arbitrary nonflat base changes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback
variable {S T U : Scheme} (E : GeneralizedEllipticCurve S)
  (g : T ⟶ S) (h : U ⟶ T) (s : 𝟙_ (Over S) ⟶ E.group)
local notation "p" => Limits.pullback.fst E.curve.hom g
local notation "q" => Limits.pullback.fst
  (Over.hom (GeneralizedEllipticCurve.curve (E.baseChange g))) h
local notation "r" => Over.Hom.left
  (GeneralizedEllipticCurve.Hom.curve (Iso.inv (E.baseChangeCompIso g h)))
local notation "d" => Limits.pullback.fst E.curve.hom (h ≫ g)

/-- The inverse associator compares the two actual projections to the original curve. -/
theorem smoothMarkingAssociator_projection : q ≫ p = r ≫ d := by
  have hh := E.baseChangeCompIso_fst_fst g h
  have hi := ((forgetCurve ⋙ Over.forget U).mapIso (E.baseChangeCompIso g h)).inv_hom_id
  change r ≫ (E.baseChangeCompIso g h).hom.curve.left = 𝟙 _ at hi
  have hp := congrArg (fun k ↦ r ≫ k) hh
  simpa only [← Category.assoc, hi, Category.id_comp] using hp

/-- Direct and successive section-line comparisons agree through the actual associator. -/
theorem smoothMarkingAssociator_lineSquare :
    LinePullbackSquare q p r d (smoothMarkingAssociator_projection E g h)
      (smoothMarkingPointLineBaseChangeIso E g s)
      (smoothMarkingPointLineBaseChangeIso (E.baseChange g) h (pullSection g s))
      (smoothMarkingPointLineBaseChangeIso E (h ≫ g) s)
      (smoothMarkingAssociatorLineIso E g h s) :=
  divisorLineSectionCompatible_square q p r d (smoothMarkingAssociator_projection E g h)
    (smoothMarkingPointLineBaseChangeIso_compatible E g s)
    (smoothMarkingPointLineBaseChangeIso_compatible (E.baseChange g) h (pullSection g s))
    (smoothMarkingPointLineBaseChangeIso_compatible E (h ≫ g) s)
    (smoothMarkingAssociatorLineIso_compatible E g h s)

/-- All existing original pole comparisons satisfy the iterated-pullback square. -/
theorem smoothMarkingAssociator_powerSquare (m : ℕ) :
    LinePullbackSquare q p r d (smoothMarkingAssociator_projection E g h)
      (smoothMarkingPowerBaseChangeIso E g s m)
      (smoothMarkingPowerBaseChangeIso (E.baseChange g) h (pullSection g s) m)
      (smoothMarkingPowerBaseChangeIso E (h ≫ g) s m)
      (smoothMarkingAssociatorPowerIso E g h s m) := by
  rw [smoothMarkingPowerBaseChangeIso_eq, smoothMarkingPowerBaseChangeIso_eq,
    smoothMarkingPowerBaseChangeIso_eq, smoothMarkingAssociatorPowerIso_eq]
  exact (smoothMarkingAssociator_lineSquare E g h s).tensorPower m

end FLT.Mazur.GeneralizedEllipticCurve
