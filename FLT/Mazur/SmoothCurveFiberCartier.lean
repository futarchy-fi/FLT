/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothFiniteSubschemeCartier
public import FLT.Mazur.ClosedIdealCartesianDegree

/-!
# Cartier equations on field fibers of smooth relative curves

The full pulled-back ideal has a locally quasi-finite closed subscheme by the
actual cartesian square of closed families. The field-curve Cartier theorem
therefore applies to arbitrary field-valued base changes and residue fibers.
This is a fiberwise assertion; lifting the equations to the base is separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve

variable {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
  (I : X.IdealSheafData) [LocallyQuasiFinite (I.subschemeι ≫ f)]

/-- The entire ideal becomes Cartier after every field-valued base change. -/
theorem effectiveCartier_field_baseChange {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ S) : EffectiveCartier (I.comap (pullback.fst f g)) := by
  let _ : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f g inferInstance
  let _ : LocallyQuasiFinite
      ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) :=
    MorphismProperty.of_isPullback
      (ClosedIdealCover.restrictionMap_base_isPullback I (pullback.fst f g)
        (IsPullback.of_hasPullback f g)) inferInstance
  exact effectiveCartier_of_smoothCurve_locallyQuasiFinite (pullback.snd f g) _

/-- Every actual residue-field fiber ideal has regular Cartier neighborhoods. -/
theorem effectiveCartier_residue_fiber (s : S) :
    EffectiveCartier (I.comap (f.fiberι s)) :=
  effectiveCartier_field_baseChange f I (S.fromSpecResidueField s)

end FLT.Mazur.FCurve
