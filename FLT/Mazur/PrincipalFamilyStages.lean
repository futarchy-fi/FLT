/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePrincipalFiniteMaps

/-!
# Stages for a finite family of incoming coordinate maps

All source charts have independent relation sets and share a target relation
set. Refinements require every coordinate square to commute.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]

/-- A finite family of lifted coordinate maps with a common target. -/
structure PrincipalFamilyStage (a : ∀ i, A i) (b : B)
    (f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b) where
  /-- The source relation set for each chart. -/
  source : ∀ i, Finset (relationIdeal R (A i))
  /-- The common target relation set. -/
  target : Finset (relationIdeal R B)
  /-- The lifted incoming maps. -/
  hom : ∀ i, PrincipalStage R (A i) (a i) (source i) →ₐ[R] PrincipalStage R B b target
  /-- Each projection recovers the original coordinate map. -/
  fac : ∀ i, (principalStageMap R B b target).comp (hom i) =
    (f i).comp (principalStageMap R (A i) (a i) (source i))

variable {a : ∀ i, A i} {b : B}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b}

/-- Refinement imposes a commuting square for every source chart. -/
instance principalFamilyStagePreorder : Preorder (PrincipalFamilyStage a b f) where
  le x y := ∃ hs : x.source ≤ y.source, ∃ ht : x.target ≤ y.target,
    ∀ i, (y.hom i).comp (principalTransition (a i) (hs i)) =
      (principalTransition b ht).comp (x.hom i)
  le_refl x := by
    refine ⟨le_rfl, le_rfl, fun i ↦ ?_⟩
    simp only [principalTransition_refl, AlgHom.comp_id, AlgHom.id_comp]
  le_trans x y z hxy hyz := by
    obtain ⟨hxyS, hxyT, hxy⟩ := hxy
    obtain ⟨hyzS, hyzT, hyz⟩ := hyz
    refine ⟨hxyS.trans hyzS, hxyT.trans hyzT, fun i ↦ ?_⟩
    calc
      (z.hom i).comp (principalTransition (a i) ((hxyS.trans hyzS) i)) =
          ((z.hom i).comp (principalTransition (a i) (hyzS i))).comp
            (principalTransition (a i) (hxyS i)) := by
        rw [AlgHom.comp_assoc, principalTransition_comp]
      _ = ((principalTransition b hyzT).comp (y.hom i)).comp
          (principalTransition (a i) (hxyS i)) := by rw [hyz]
      _ = (principalTransition b hyzT).comp
          ((principalTransition b hxyT).comp (x.hom i)) := by
        rw [AlgHom.comp_assoc, hxy]
      _ = (principalTransition b (hxyT.trans hyzT)).comp (x.hom i) := by
        rw [← AlgHom.comp_assoc, principalTransition_comp]

/-- Every collection of source bounds admits simultaneous lifts. -/
theorem exists_principalFamilyStage (s : ∀ i, Finset (relationIdeal R (A i)))
    (t : Finset (relationIdeal R B)) :
    ∃ x : PrincipalFamilyStage a b f, x.source = s ∧ t ≤ x.target := by
  obtain ⟨q, htq, g, hg⟩ := exists_principalStageMap_finite_lift b A a f s t
  exact ⟨⟨s, q, g, hg⟩, rfl, htq⟩

/-- A compatible family stage exists, including for the empty family. -/
instance principalFamilyStageNonempty : Nonempty (PrincipalFamilyStage a b f) := by
  obtain ⟨x, _, _⟩ := exists_principalFamilyStage (a := a) (b := b) (f := f) (fun _ ↦ ∅) ∅
  exact ⟨x⟩

end FLT.Mazur.FiniteTypeRelationModel
