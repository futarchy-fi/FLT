/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePrincipalMaps

/-!
# The ordered stages of a principal coordinate map

An index records finite relation sets on both charts and a lift of the
original map. Refinement requires a commuting square of model maps. This
orders actual finite lifts, rather than choosing unrelated maps at each stage.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B]

/-- Transition on a principal model, with the original denominator as parameter. -/
abbrev principalTransition (a : A) {s t : Finset (relationIdeal R A)} (h : s ≤ t) :
    PrincipalStage R A a s →ₐ[R] PrincipalStage R A a t :=
  FiniteRelationLocalization.transition R (relationIdeal R A)
    (principalRepresentative R A a) h

/-- A reflexive principal transition is the identity. -/
@[simp] theorem principalTransition_refl (a : A) (s : Finset (relationIdeal R A)) :
    principalTransition a (le_refl s) = AlgHom.id R (PrincipalStage R A a s) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (FiniteRelationModel.relations (relationIdeal R A) s)
      (principalRepresentative R A a)))
  ext x
  change principalTransition a (le_refl s)
    (algebraMap _ (PrincipalStage R A a s) x) = algebraMap _ (PrincipalStage R A a s) x
  rw [FiniteRelationLocalization.transition_algebraMap]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [FiniteRelationModel.transition_mk]

/-- Principal transitions compose along inclusions of finite relation sets. -/
theorem principalTransition_comp (a : A) {s t q : Finset (relationIdeal R A)}
    (h : s ≤ t) (k : t ≤ q) :
    (principalTransition a k).comp (principalTransition a h) =
      principalTransition a (h.trans k) :=
  FiniteRelationLocalization.transition_comp R (relationIdeal R A)
    (principalRepresentative R A a) h k

/-- A finite model of one coordinate map, with its compatibility at the limit. -/
structure PrincipalMapStage (a : A) (b : B)
    (f : Localization.Away a →ₐ[R] Localization.Away b) where
  /-- Finite relations imposed on the source chart. -/
  source : Finset (relationIdeal R A)
  /-- Finite relations imposed on the target chart. -/
  target : Finset (relationIdeal R B)
  /-- The coordinate map between the two finite principal models. -/
  hom : PrincipalStage R A a source →ₐ[R] PrincipalStage R B b target
  /-- Projection recovers the original coordinate map. -/
  fac : (principalStageMap R B b target).comp hom = f.comp (principalStageMap R A a source)

variable {a : A} {b : B} {f : Localization.Away a →ₐ[R] Localization.Away b}

/-- Refinements are precisely the commuting squares of principal model transitions. -/
instance principalMapStagePreorder : Preorder (PrincipalMapStage a b f) where
  le x y := ∃ hs : x.source ≤ y.source, ∃ ht : x.target ≤ y.target,
    y.hom.comp (principalTransition a hs) = (principalTransition b ht).comp x.hom
  le_refl x := by
    refine ⟨le_rfl, le_rfl, ?_⟩
    simp only [principalTransition_refl, AlgHom.comp_id, AlgHom.id_comp]
  le_trans x y z hxy hyz := by
    obtain ⟨hxyS, hxyT, hxy⟩ := hxy
    obtain ⟨hyzS, hyzT, hyz⟩ := hyz
    refine ⟨hxyS.trans hyzS, hxyT.trans hyzT, ?_⟩
    calc
      z.hom.comp (principalTransition a (hxyS.trans hyzS)) =
          (z.hom.comp (principalTransition a hyzS)).comp
            (principalTransition a hxyS) := by
        rw [AlgHom.comp_assoc, principalTransition_comp]
      _ = ((principalTransition b hyzT).comp y.hom).comp
          (principalTransition a hxyS) := by rw [hyz]
      _ = (principalTransition b hyzT).comp ((principalTransition b hxyT).comp x.hom) := by
        rw [AlgHom.comp_assoc, hxy]
      _ = (principalTransition b (hxyT.trans hyzT)).comp x.hom := by
        rw [← AlgHom.comp_assoc, principalTransition_comp]

/-- Every pair of lower bounds admits an actual finite coordinate model. -/
theorem exists_principalMapStage (s : Finset (relationIdeal R A))
    (t : Finset (relationIdeal R B)) :
    ∃ x : PrincipalMapStage a b f, x.source = s ∧ t ≤ x.target := by
  obtain ⟨q, htq, F, hF⟩ := exists_principalStageMap_lift b a f s t
  exact ⟨⟨s, q, F, hF⟩, rfl, htq⟩

/-- There is a model even when no initial relations have been specified. -/
instance principalMapStageNonempty : Nonempty (PrincipalMapStage a b f) := by
  obtain ⟨x, _, _⟩ := exists_principalMapStage (a := a) (b := b) (f := f) ∅ ∅
  exact ⟨x⟩

end FLT.Mazur.FiniteTypeRelationModel
