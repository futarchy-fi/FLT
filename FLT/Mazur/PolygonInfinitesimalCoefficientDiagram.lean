/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalFamily
public import FLT.Mazur.PolygonSmoothingCoefficientSquares
public import FLT.Mazur.EquifiberedGluingBaseChange

/-!
# Coefficient change of the complete infinitesimal cyclic diagram

The actual coefficient maps define a natural transformation on all charts and
edges. Every object square over the base is cartesian, hence so is every arrow
square. This includes both arrows of the two-gon.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open PolygonSmoothing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (t : R) (n : ℕ)

/-- The actual coefficient transformation on the complete cyclic diagram. -/
def coefficientDiagram : diagram S (algebraMap R S t) n ⟶ diagram R t n where
  app j := match j with
    | .left _ => edgeCoefficient R S
    | .right _ => chartCoefficient R S t
  naturality := by
    intro i j f
    cases f with
    | id i => simp
    | fst i => exact leftBranch_coefficient R S t
    | snd i => exact precedingBranch_coefficient R S t

/-- Every object of the complete diagram has the correct coefficient pullback. -/
theorem coefficientDiagram_base (j : WalkingMultispan (PolygonCyclicAtlas.shape n)) :
    IsPullback ((coefficientDiagram R S t n).app j)
      ((baseCocone S (algebraMap R S t) n).ι.app j)
      ((baseCocone R t n).ι.app j) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  cases j with
  | left i => exact edgeCoefficient_isPullback R S
  | right i => exact chartCoefficient_isPullback R S t

/-- Every full overlap square is cartesian, by cancellation of the base squares. -/
theorem coefficientDiagram_equifibered : (coefficientDiagram R S t n).Equifibered := by
  intro i j f
  apply IsPullback.flip
  apply ((coefficientDiagram_base R S t n j).paste_vert_iff
    ((coefficientDiagram R S t n).naturality f).symm).mp
  simpa only [Cocone.w] using coefficientDiagram_base R S t n i

end FLT.Mazur.PolygonInfinitesimal
