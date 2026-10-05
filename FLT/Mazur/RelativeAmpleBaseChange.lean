/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAmpleConverse
public import FLT.Mazur.RelativeSectionAmpleBaseChange

/-!
# Arbitrary base change of closed projective power presentations

Properness and relative section ampleness both survive base change. The proper
ample converse supplies a positive-power closed presentation on every affine
open of the new base, without a supplied global presentation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
variable {X Y S T : Scheme} {f : X ⟶ S} {g : T ⟶ S}
  {p : Y ⟶ X} {q : Y ⟶ T} {L : X.Modules}

/-- A cartesian square transports all affine-local closed power presentations. -/
theorem RelativeAmple.of_isPullback (hL : RelativeAmple f L)
    (hline : LocallyFreeRankOne L) (sq : IsPullback p q f g) :
    RelativeAmple q ((Scheme.Modules.pullback p).obj L) := by
  let := hL.isProper
  have : IsProper q := MorphismProperty.of_isPullback sq inferInstance
  exact ((hL.relativelyAmpleLineBundle hline).of_isPullback sq).relativeAmple

/-- Relative ampleness of an invertible sheaf survives arbitrary base change. -/
theorem RelativeAmple.baseChange (hL : RelativeAmple f L)
    (hline : LocallyFreeRankOne L) (g : T ⟶ S) :
    RelativeAmple (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L) :=
  hL.of_isPullback hline (IsPullback.of_hasPullback f g)

end FLT.Mazur.FCurve
