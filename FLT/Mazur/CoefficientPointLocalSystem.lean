/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientStageColimit
public import FLT.Mazur.PointLocalizedRingColimit
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The actual local base system of finite coefficient models

A point of the original affine base gives local Noetherian coefficient rings,
local transition maps and their colimit. The rings and transitions are also
identified with the stalks and stalk maps of the actual coefficient spectra.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CoefficientPointLocalSystem
open Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A : Type u} [CommRing A] (R : Subalgebra ℤ A)
  (P : Ideal A) [P.IsPrime]

/-- The point of a coefficient spectrum lying under the chosen original point. -/
def point (i : CoefficientStage R) : PrimeSpectrum i.val :=
  ⟨P.comap i.val.val.toRingHom, inferInstance⟩

/-- The local coefficient ring at the actual induced point. -/
abbrev LocalRing (i : CoefficientStage R) :=
  PointLocalizedRingDiagram.Stage (coefficientStageCocone R) P i

instance localRing_noetherian (i : CoefficientStage R) :
    IsNoetherianRing (LocalRing R P i) := by
  let _ : IsNoetherianRing i.val := Algebra.FiniteType.isNoetherianRing ℤ i.val
  exact inferInstanceAs (IsNoetherianRing (Localization.AtPrime (point R P i).asIdeal))

/-- The diagram uses the original coefficient inclusions localized at their induced points. -/
abbrev diagram : CoefficientStage R ⥤ CommRingCat.{u} :=
  PointLocalizedRingDiagram.diagram (coefficientStageCocone R) P

/-- Its canonical cocone has vertex the original affine base's local ring. -/
abbrev cocone : Cocone (diagram R P) :=
  PointLocalizedRingDiagram.cocone (coefficientStageCocone R) P

instance transition_isLocalHom {i j : CoefficientStage R} (f : i ⟶ j) :
    IsLocalHom ((diagram R P).map f).hom :=
  PointLocalizedRingDiagram.transition_isLocalHom (coefficientStageCocone R) P f

/-- The actual finite coefficient local rings recover the original base local ring. -/
def isColimit [Algebra.FiniteType ℤ R] : IsColimit (cocone R P) :=
  PointLocalizedRingDiagram.localizedIsColimit (coefficientStageCocone R) P
    (coefficientStageIsColimit R)

/-- Every local coefficient ring is the stalk of the actual coefficient spectrum. -/
def stalkIso (i : CoefficientStage R) :
    (Spec (.of i.val)).presheaf.stalk (point R P i) ≅ .of (LocalRing R P i) :=
  Spec.stalkIso (.of i.val) (point R P i)

/-- Transition maps identify with the actual stalk maps between coefficient spectra. -/
def transitionStalkIso {i j : CoefficientStage R} (f : i ⟶ j) :
    Arrow.mk ((Spec.map ((coefficientStageDiagram R).map f)).stalkMap (point R P j)) ≅
      Arrow.mk ((diagram R P).map f) :=
  Scheme.arrowStalkMapSpecIso ((coefficientStageDiagram R).map f) (point R P j)

end FLT.Mazur.CoefficientPointLocalSystem
