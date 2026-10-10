/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationDetection
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# An arbitrary quotient is the colimit of its finite-relation stages

The diagram is filtered by union of finite relation sets. Surjectivity and
finite detection of equality prove the actual colimit universal property.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.FiniteRelationModel

universe u v

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P)

/-- The filtered ring diagram obtained by imposing more relations. -/
def ringDiagram : Finset I ⥤ CommRingCat.{v} where
  obj s := .of (Stage I s)
  map f := CommRingCat.ofHom (transition R I (leOfHom f)).toRingHom
  map_id s := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    rfl
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (transition_comp R I (leOfHom f) (leOfHom g)).symm

/-- The canonical maps to the full quotient form a cocone. -/
def quotientCocone : Cocone (ringDiagram R I) where
  pt := .of (P ⧸ I)
  ι.app s := CommRingCat.ofHom (toQuotient R I s).toRingHom
  ι.naturality s t f := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (toQuotient_comp R I (leOfHom f))

/-- The underlying quotient set has the finite-relation colimit property. -/
def quotientTypesIsColimit :
    IsColimit ((forget CommRingCat).mapCocone (quotientCocone R I)) := by
  classical
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨y, hy⟩ := toQuotient_surjective R I ∅ x
    exact ⟨∅, y, hy.symm⟩
  · intro s x y h
    obtain ⟨t, hst, ht⟩ := exists_transition_eq R I s x y h
    exact ⟨t, homOfLE hst, ht⟩

/-- Imposing all relations is the filtered colimit in commutative rings. -/
def quotientIsColimit : IsColimit (quotientCocone R I) := by
  let _ := reflectsColimit_of_reflectsIsomorphisms (ringDiagram R I) (forget CommRingCat)
  exact isColimitOfReflects (forget CommRingCat) (quotientTypesIsColimit R I)

end FLT.Mazur.FiniteRelationModel
