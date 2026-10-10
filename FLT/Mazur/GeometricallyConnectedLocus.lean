/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricallyConnectedDescent

/-!
# The geometrically connected fiber locus

The locus is defined by the actual residue-field fibers. It commutes with
arbitrary cartesian base change: the reverse inclusion uses surjective
descent along the induced extension of residue fields. In particular, the
image of a base with geometrically connected recovery lies in this locus.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Base points whose actual scheme-theoretic fibers are geometrically connected. -/
def geometricallyConnectedLocus {X S : Scheme.{u}} (f : X ⟶ S) : Set S :=
  {s | GeometricallyConnected (f.fiberToSpecResidueField s)}

/-- The locus is the whole base precisely for a geometrically connected morphism. -/
theorem geometricallyConnectedLocus_eq_univ_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    geometricallyConnectedLocus f = Set.univ ↔ GeometricallyConnected f := by
  rw [Set.eq_univ_iff_forall, GeometricallyConnected.iff_geometricallyConnected_fiber]
  rfl

/-- An arbitrary cartesian recovery pulls the fiber locus back exactly. -/
theorem geometricallyConnectedLocus_of_isPullback {P X T S : Scheme.{u}}
    {a : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (h : IsPullback a q f g) :
    geometricallyConnectedLocus q = g ⁻¹' geometricallyConnectedLocus f := by
  ext t
  exact MorphismProperty.iff_of_isPullback
    (P := @GeometricallyConnected) (Q := @Surjective)
    (isPullback_fiberToSpecResidueField_of_isPullback h t).flip inferInstance

/-- A geometrically connected recovery forces every point of the base image into the locus. -/
theorem range_subset_geometricallyConnectedLocus {P X T S : Scheme.{u}}
    {a : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (h : IsPullback a q f g) [GeometricallyConnected q] :
    Set.range g ⊆ geometricallyConnectedLocus f := by
  rintro _ ⟨t, rfl⟩
  have ht : t ∈ geometricallyConnectedLocus q :=
    inferInstanceAs (GeometricallyConnected (q.fiberToSpecResidueField t))
  rwa [geometricallyConnectedLocus_of_isPullback h] at ht

/-- A restriction has geometrically connected fibers exactly when its open lies in the locus. -/
theorem geometricallyConnected_restrict_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Opens) :
    GeometricallyConnected (f ∣_ U) ↔ (U : Set S) ⊆ geometricallyConnectedLocus f := by
  rw [← geometricallyConnectedLocus_eq_univ_iff,
    geometricallyConnectedLocus_of_isPullback (isPullback_morphismRestrict f U).flip,
    Set.eq_univ_iff_forall]
  exact ⟨fun h x hx ↦ h ⟨x, hx⟩, fun h x ↦ h x.property⟩

end FLT.Mazur.Approximation
