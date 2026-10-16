/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCompleteFrameComparison

/-!
# Completeness transfers to distinct frames of the same finite size

A complete frame identifies the entire geometric fiber with its finite label
set. Every other distinct frame with that label set is then complete as well.
This is a statement on a specified fiber, not on a neighborhood of that fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {K : Type} [Field K] {b : Spec (.of K) ⟶ S}

/-- Distinct coordinates give distinct points of the entire geometric fiber. -/
theorem geometricCoordinate_point_injective (t : Over.mk b ⟶ distinctScheme E I) :
    Function.Injective (fun i ↦ geometricCoordinate E I t i default) := by
  intro i j hij
  have he : geometricCoordinate E I t i = geometricCoordinate E I t j := congrArg Subtype.val
    (EtaleGeometricSections.section_ext (pullback.snd E.hom b)
      (s := ⟨geometricCoordinate E I t i, geometricCoordinate_snd E I t i⟩)
      (t := ⟨geometricCoordinate E I t j, geometricCoordinate_snd E I t j⟩) hij)
  let _ : Nonempty (Over.mk b).left := inferInstanceAs (Nonempty (Spec (.of K)))
  apply distinctCoordinate_injective E I t
  apply Over.OverMorphism.ext
  simpa only [geometricCoordinate_fst] using
    congrArg (fun f ↦ f ≫ pullback.fst E.hom b) he

/-- A distinct frame with the size of a complete frame must enumerate the whole fiber. -/
theorem complete_of_complete_frame (a t : Over.mk b ⟶ distinctScheme E I)
    (ha : Function.Bijective (fun i ↦ geometricCoordinate E I a i default)) :
    Function.Bijective (fun i ↦ geometricCoordinate E I t i default) := by
  let h := Equiv.ofBijective _ ha
  have ht := geometricCoordinate_point_injective E I t
  refine ⟨ht, ?_⟩
  have hi : Function.Injective (fun i ↦ h.symm (geometricCoordinate E I t i default)) :=
    h.symm.injective.comp ht
  intro x
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hi (h.symm x)
  exact ⟨i, h.symm.injective hi⟩

end FLT.Mazur.RelativeOrderedTuples
