/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluedCartesian
public import FLT.Mazur.FiniteRelationSpectrum
public import FLT.Mazur.ClosedImmersionCartesianCover

/-!
# Closed immersion transitions of the glued inverse system

Whole-chart cartesian squares identify each restriction with a surjective
finite-relation spectrum map. Thus the nonaffine inverse system has closed
immersion transitions, in particular affine transitions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Small.{u} ι]
  (x y : PrincipalOccurrenceGluingStage e) (hxy : x ≤ y)

/-- The whole-chart refinement is a closed immersion. -/
instance principalOccurrenceGluingChartMap_isClosedImmersion (i : Shrink.{u} ι) :
    IsClosedImmersion (principalOccurrenceGluingChartMap e x y hxy i) := by
  unfold principalOccurrenceGluingChartMap principalOccurrenceAmbientTransition
  exact IsClosedImmersion.spec_of_surjective _
    (FiniteRelationModel.transition_surjective R (relationIdeal R (A ((equivShrink.{u} ι).symm i)))
      (principalOccurrence_source_mono hxy ((equivShrink.{u} ι).symm i)))

/-- Each global refinement is a closed immersion. -/
instance principalOccurrenceGluedTransition_isClosedImmersion :
    IsClosedImmersion (principalOccurrenceGluedTransition e x y hxy) :=
  isClosedImmersion_of_cartesian_cover (principalOccurrenceGluedTransition e x y hxy)
    (principalOccurrenceStageGlueData e x).openCover
    (fun i ↦ (principalOccurrenceStageGlueData e y).U i)
    (fun i ↦ (principalOccurrenceStageGlueData e y).ι i)
    (principalOccurrenceGluingChartMap e x y hxy)
    (fun i ↦ (principalOccurrenceGluedTransition_isPullback e x y hxy i).flip)
    (principalOccurrenceGluingChartMap_isClosedImmersion e x y hxy)

/-- Every arrow in the constructed inverse diagram is a closed immersion. -/
instance principalOccurrenceGluedDiagram_map_isClosedImmersion
    {x y : (PrincipalOccurrenceGluingStage e)ᵒᵖ} (g : x ⟶ y) :
    IsClosedImmersion ((principalOccurrenceGluedDiagram e).map g) :=
  principalOccurrenceGluedTransition_isClosedImmersion e y.unop x.unop (leOfHom g.unop)

/-- The actual glued inverse system has affine transition maps. -/
instance principalOccurrenceGluedDiagram_map_isAffineHom
    {x y : (PrincipalOccurrenceGluingStage e)ᵒᵖ} (g : x ⟶ y) :
    IsAffineHom ((principalOccurrenceGluedDiagram e).map g) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel
