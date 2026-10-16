/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteJointFrameEnumeration
public import FLT.Mazur.RelativeDistinctSubframe

/-!
# A common distinct frame for arbitrary geometric frames

The union of the original section morphisms is an actual distinct scheme test.
It contains both frames and has at most the sum of their sizes. Completeness of
the full fiber is unnecessary, even when both original frames are incomplete.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  {I J : Type} [Fintype I] [Fintype J]
  {T : Over S} [Subsingleton T.left] [Nonempty T.left]
  (a : T ⟶ distinctScheme E I) (b : T ⟶ distinctScheme E J)

/-- The actual union of two independent geometric frames, with both exact subframe equations. -/
theorem exists_joint_geometric_frame :
    ∃ (n : ℕ) (_ : n ≤ Fintype.card I + Fintype.card J)
      (α : I ↪ Fin n) (β : J ↪ Fin n) (w : T ⟶ distinctScheme E (Fin n)),
      w ≫ subframe E α = a ∧ w ≫ subframe E β = b ∧
      (∀ k, (∃ i, α i = k) ∨ ∃ j, β j = k) := by
  obtain ⟨n, hn, α, β, t, ha, hb, ht⟩ := finite_joint_frame_enumeration
    (fun i ↦ a ≫ distinctCoordinate E I i) (fun j ↦ b ≫ distinctCoordinate E J j)
    (distinctCoordinate_injective E I a) (distinctCoordinate_injective E J b)
  refine ⟨n, hn, α, β, distinctLift E (Fin n) t t.injective, ?_, ?_, ht⟩
  · apply distinct_hom_ext E I
    intro i
    rw [Category.assoc, subframe_coordinate, distinctLift_coordinate]
    exact ha i
  · apply distinct_hom_ext E J
    intro j
    rw [Category.assoc, subframe_coordinate, distinctLift_coordinate]
    exact hb j

end FLT.Mazur.RelativeOrderedTuples
