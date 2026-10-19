/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameMissingSection

/-!
# Strict extensions of the actual geometric frame

Append a missing original section, retaining every existing coordinate and
its label. An incomplete frame over a separably closed field therefore has
an actual larger distinct tuple over exactly the same geometric endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {K : Type} [Field K]
  {b : Spec (.of K) ⟶ S} (t : Over.mk b ⟶ distinctScheme E I)
  (a : Over.mk b ⟶ E) (ha : ∀ i, a ≠ t ≫ distinctCoordinate E I i)

include ha in
omit [Etale E.hom] in
/-- Appending the missing section is injective on all old and new labels. -/
theorem appended_coordinates_injective :
    Function.Injective (fun j : Option I ↦ j.elim a (fun i ↦ t ≫ distinctCoordinate E I i)) := by
  let _ : Nonempty (Over.mk b).left := inferInstanceAs (Nonempty (Spec (.of K)))
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact (ha j h).elim
  | some i =>
    cases j with
    | none => exact (ha i h.symm).elim
    | some j => exact congrArg some (distinctCoordinate_injective E I t h)

/-- The constructed extension is a tuple of original arrows, with one additional label. -/
def appendOriginalFrame : Over.mk b ⟶ distinctScheme E (Option I) := by
  let _ : Subsingleton (Over.mk b).left := inferInstanceAs (Subsingleton (Spec (.of K)))
  exact distinctLift E (Option I)
    (fun j : Option I ↦ j.elim a (fun i ↦ t ≫ distinctCoordinate E I i))
    (appended_coordinates_injective E I t a ha)

/-- The added coordinate is precisely the chosen missing arrow. -/
@[reassoc] theorem appendOriginalFrame_none :
    appendOriginalFrame E I t a ha ≫ distinctCoordinate E (Option I) none = a := by
  let _ : Subsingleton (Over.mk b).left := inferInstanceAs (Subsingleton (Spec (.of K)))
  exact distinctLift_coordinate E (Option I) _
    (appended_coordinates_injective E I t a ha) none

/-- All existing original coordinates are preserved, rather than replaced by a larger cutoff. -/
@[reassoc] theorem appendOriginalFrame_some (i : I) :
    appendOriginalFrame E I t a ha ≫ distinctCoordinate E (Option I) (some i) =
      t ≫ distinctCoordinate E I i := by
  let _ : Subsingleton (Over.mk b).left := inferInstanceAs (Subsingleton (Spec (.of K)))
  exact distinctLift_coordinate E (Option I) _
    (appended_coordinates_injective E I t a ha) (some i)

variable [IsSepClosed K]

/-- Failure of completeness constructs a strict extension over the unchanged field and endpoint. -/
theorem exists_strict_original_extension
    (ht : ¬ Function.Bijective (fun i ↦ geometricCoordinate E I t i default)) :
    ∃ v : Over.mk b ⟶ distinctScheme E (Option I),
      (∀ i, v ≫ distinctCoordinate E (Option I) (some i) = t ≫ distinctCoordinate E I i) ∧
      ∀ i, v ≫ distinctCoordinate E (Option I) none ≠ t ≫ distinctCoordinate E I i := by
  obtain ⟨a, ha⟩ := exists_missing_original_section E I t ht
  refine ⟨appendOriginalFrame E I t a ha, appendOriginalFrame_some E I t a ha, ?_⟩
  intro i
  rw [appendOriginalFrame_none]
  exact ha i

end FLT.Mazur.RelativeOrderedTuples
