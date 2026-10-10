/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFieldCohomologyBaseChange
public import FLT.Mazur.CurveEulerCharacteristic
public import FLT.Mazur.ModulePullbackUnitCoherence

/-!
# Curve degree is invariant under field base change

The actual H0 and H1 dimension comparisons preserve the cohomological Euler
characteristic and degree. The result needs only properness and quasi-coherence;
it applies in particular to actual line sheaves on smooth proper curves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {k K : Type} [Field k] [Field K] {P X : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ Spec (CommRingCat.of K)}
  {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f]
  {g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]

include h

/-- The H0 minus H1 Euler characteristic is unchanged by field base change. -/
theorem curveEulerCharacteristic_field_baseChange :
    curveEulerCharacteristic q ((pullback p).obj M) = curveEulerCharacteristic f M := by
  unfold curveEulerCharacteristic
  rw [proper_field_cohomology_finrank h M 0, proper_field_cohomology_finrank h M 1]

/-- Actual cohomological sheaf degree is unchanged by field base change. -/
theorem curveSheafDegree_field_baseChange :
    curveSheafDegree q ((pullback p).obj M) = curveSheafDegree f M := by
  let _ : (structureModule X).IsFinitePresentation := unitSheaf_isFinitePresentation X
  have hs : curveEulerCharacteristic q (structureModule P) =
      curveEulerCharacteristic f (structureModule X) :=
    (curveEulerCharacteristic_iso q (modulePullbackUnitIso p)).symm.trans
      (curveEulerCharacteristic_field_baseChange h (structureModule X))
  change curveEulerCharacteristic q ((pullback p).obj M) -
    curveEulerCharacteristic q (structureModule P) =
      curveEulerCharacteristic f M - curveEulerCharacteristic f (structureModule X)
  rw [curveEulerCharacteristic_field_baseChange h M, hs]

end FLT.Mazur.FCurve
