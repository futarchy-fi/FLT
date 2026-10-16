/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCompleteSubframe
public import FLT.Mazur.RelativeFrameCompletenessTransfer

/-!
# Completeness from exclusion of larger original frames

An n-frame is complete if its base point admits no (n+1)-frame. This uses
an enumeration of the whole geometric fiber, not a selected finite branch.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] {K : Type} [Field K] [IsSepClosed K]
  {b : Spec (.of K) ⟶ S} (n : ℕ)

omit [Etale E.hom] [QuasiCompact E.hom] [IsSepClosed K] in
/-- Excluding larger frames bounds the size of an actual complete geometric enumeration. -/
theorem complete_frame_size_le_of_no_larger
    (hn : b default ∉ Set.range (distinctScheme E (Fin (n + 1))).hom)
    {m : ℕ} (a : Over.mk b ⟶ distinctScheme E (Fin m)) : m ≤ n := by
  by_contra h
  have hnm : n + 1 ≤ m := Nat.lt_of_not_ge h
  let ι : Fin (n + 1) ↪ Fin m := Fin.castLEEmb hnm
  let t := a ≫ subframe E ι
  apply hn
  refine ⟨t.left (default : Spec (.of K)), ?_⟩
  exact congrArg (fun f ↦ f (default : Spec (.of K))) t.w

/-- An original distinct frame of maximal allowed size enumerates the entire geometric fiber. -/
theorem geometric_complete_of_no_larger
    (t : Over.mk b ⟶ distinctScheme E (Fin n))
    (hn : b default ∉ Set.range (distinctScheme E (Fin (n + 1))).hom) :
    Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) t i default) := by
  obtain ⟨m, a, ha⟩ := exists_complete_geometric_tuple E b
  have hmn := complete_frame_size_le_of_no_larger E n hn a
  have hnm : n ≤ m := by
    simpa only [Fintype.card_fin] using cardinality_le_complete_frame E a ha t
  obtain rfl := Nat.le_antisymm hmn hnm
  exact complete_of_complete_frame E (Fin m) a t ha

end FLT.Mazur.RelativeOrderedTuples
