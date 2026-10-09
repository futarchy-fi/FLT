/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.MorphismProperty.Descent

/-!
# Surjective descent of geometric connectedness

A point of a nonempty base change supplies a residue field over which the
family is connected. Surjectivity of field extensions then detects connectedness
of the original space. Applying this after every field-valued base change
proves descent along arbitrary surjective scheme morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A nonempty base change detecting geometric connectedness detects connectedness over a field. -/
theorem connectedSpace_of_cartesian_nonempty_field {K : Type u} [Field K]
    {X T P : Scheme.{u}} {f : X ⟶ Spec (.of K)} {g : T ⟶ Spec (.of K)}
    {a : P ⟶ X} {q : P ⟶ T} (h : IsPullback a q f g)
    [Nonempty T] [GeometricallyConnected q] : ConnectedSpace X := by
  let t : T := Classical.choice inferInstance
  let b := T.fromSpecResidueField t
  let r := pullback.fst q b ≫ a
  have hc := (IsPullback.of_hasPullback q b).paste_horiz h
  have : Surjective (b ≫ g) := inferInstance
  have : Surjective r := MorphismProperty.of_isPullback hc.flip inferInstance
  have : ConnectedSpace ↥(pullback q b) :=
    GeometricallyConnected.geometrically_connectedSpace b _ _ (.of_hasPullback _ _)
  exact r.surjective.connectedSpace r.continuous

/-- Geometric connectedness descends from a surjective base change. -/
theorem geometricallyConnected_of_surjective_pullback {X T S : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) [Surjective g]
    [GeometricallyConnected (pullback.fst g f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  have : Nonempty ↥(pullback g y) :=
    (pullback.snd g y).surjective.nonempty
  have : ConnectedSpace ↥(pullback y f) :=
    connectedSpace_of_cartesian_nonempty_field (isPullback_map_snd_snd g y f)
  exact (pullbackSymmetry f y).hom.homeomorph.connectedSpace_iff.mpr inferInstance

/-- Geometric connectedness satisfies descent along every surjective scheme morphism. -/
instance geometricallyConnected_descendsAlong_surjective :
    MorphismProperty.DescendsAlong @GeometricallyConnected.{u} @Surjective.{u} where
  of_isPullback {P T X S} {q a g f} h hg hq := by
    have : Surjective g := hg
    have : GeometricallyConnected (pullback.fst g f) := by
      rwa [← MorphismProperty.cancel_left_of_respectsIso
        @GeometricallyConnected h.isoPullback.hom, h.isoPullback_hom_fst]
    exact geometricallyConnected_of_surjective_pullback f g

end FLT.Mazur.Approximation
