/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationDetection
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The filtered colimit of localized finite-relation models

The localized quotient is recovered exactly, using surjectivity and the
finite detection of equality after clearing denominators. The index is the
same finite-relation index as for the ambient affine chart.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.FiniteRelationLocalization

universe u v

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

/-- Principal-open rings, indexed by the ambient chart's finite relation sets. -/
def ringDiagram : Finset I ⥤ CommRingCat.{v} where
  obj s := .of (Stage I r s)
  map f := CommRingCat.ofHom (transition R I r (leOfHom f)).toRingHom
  map_id s := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (Ideal.Quotient.mk (FiniteRelationModel.relations I s) r))
    apply RingHom.ext
    intro x
    change transition R I r le_rfl (algebraMap _ (Stage I r s) x) =
      algebraMap _ (Stage I r s) x
    rw [transition_algebraMap]
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [FiniteRelationModel.transition_mk]
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (transition_comp R I r (leOfHom f) (leOfHom g)).symm

/-- The compatible projections onto the limiting principal-open ring. -/
def quotientCocone : Cocone (ringDiagram R I r) where
  pt := .of (Quotient I r)
  ι.app s := CommRingCat.ofHom (toQuotient R I r s).toRingHom
  ι.naturality s t f := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (toQuotient_comp R I r (leOfHom f))

/-- Localization of the full quotient is the filtered colimit of the localized stages. -/
def quotientIsColimit : IsColimit (quotientCocone R I r) := by
  classical
  let _ := reflectsColimit_of_reflectsIsomorphisms (ringDiagram R I r) (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨y, hy⟩ := toQuotient_surjective R I r ∅ x
    exact ⟨∅, y, hy.symm⟩
  · intro s x y h
    obtain ⟨t, hst, ht⟩ := exists_transition_eq R I r s x y h
    exact ⟨t, homOfLE hst, ht⟩

end FLT.Mazur.FiniteRelationLocalization
