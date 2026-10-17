/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteTargetBaseChange

/-!
# Finiteness on the entire exact finite target locus

Zariski locality combines all finite target neighborhoods. An open lies in
this locus exactly when the whole original morphism over that open is finite.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} (p : D ⟶ A)

/-- Every open contained in the actual finite target locus has finite whole preimage. -/
theorem finite_restrict_of_le_finiteTarget (B : A.Opens) (hB : B ≤ finiteTargetOpen p) :
    IsFinite (p ∣_ B) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
  intro x
  obtain ⟨V, hV, hxV⟩ := (mem_finiteTargetOpen p (B.ι x)).mp (hB x.property)
  let _ := hV
  exact ⟨B.ι ⁻¹ᵁ V, hxV,
    finite_restrict_of_isPullback (isPullback_morphismRestrict p B).flip V⟩

/-- The finite target locus is itself an actual finite neighborhood. -/
theorem finite_restrict_finiteTarget : IsFinite (p ∣_ finiteTargetOpen p) :=
  finite_restrict_of_le_finiteTarget p _ le_rfl

/-- Open containment in the locus is an exact geometric finiteness test. -/
theorem le_finiteTargetOpen_iff (B : A.Opens) :
    B ≤ finiteTargetOpen p ↔ IsFinite (p ∣_ B) := by
  refine ⟨finite_restrict_of_le_finiteTarget p B, fun h x hx ↦ ?_⟩
  exact (mem_finiteTargetOpen p x).mpr ⟨B, h, hx⟩

/-- Full finite-neighborhood coverage implies finiteness of the original morphism. -/
theorem finiteTargetOpen_eq_top_iff : finiteTargetOpen p = ⊤ ↔ IsFinite p := by
  constructor
  · intro h
    apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
    intro x
    obtain ⟨B, hB, hxB⟩ := (mem_finiteTargetOpen p x).mp (by rw [h]; trivial)
    exact ⟨B, hxB, hB⟩
  · intro h
    let _ := h
    exact finiteTargetOpen_eq_top p

/-- Every cartesian test landing in the exact finite locus has finite whole pullback. -/
theorem finite_pullback_of_range_subset {T P : Scheme} {a : P ⟶ D} {b : P ⟶ T}
    {g : T ⟶ A} (H : IsPullback a b p g) (hg : Set.range g ⊆ finiteTargetOpen p) :
    IsFinite b := by
  apply (finiteTargetOpen_eq_top_iff b).mp
  apply top_unique
  intro x _
  exact preimage_finiteTargetOpen_le H (hg ⟨x, rfl⟩)

end FLT.Mazur.SchemeOpenEnvelope
