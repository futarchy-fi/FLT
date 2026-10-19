/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedCompleteInterior
public import FLT.Mazur.EquivalenceRelationFiniteCompleteInterior

/-!
# Transfer of constructed finite neighborhoods to prescribed frames

A complete frame over a finite original endpoint supplies a complete interior
at every independently prescribed equally sized related frame. The second
endpoint need not be known to have a finite neighborhood. The original field,
labels and relation arrow are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [Etale q]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o o' : I)
  {K : Type} [Field K]
  (u : Spec (.of K) ⟶ source p q I o) (v : Spec (.of K) ⟶ source p q I o')
  (a : Spec (.of K) ⟶ D) (ha : a ≫ p = u ≫ first p q I o)
  (hb : a ≫ q = v ≫ first p q I o')
include e a ha hb

/-- A full original arrow preserves interior completeness across independent labels. -/
theorem mixed_original_arrow_interior_iff :
    u default ∈ completeInterior (p := p) (q := q) I o ↔
      v default ∈ completeInterior (p := p) (q := q) I o' := by
  let z := MixedFrames.lift p q I I o o' u v a ha hb
  have H := congrArg (fun O ↦ z default ∈ O)
    (MixedFrames.completeInterior_mixed_invariant e I o o')
  have h₁ : MixedFrames.fst p q I I o o' (z default) = u default :=
    congrArg (fun f : Spec (.of K) ⟶ source p q I o ↦ f default)
      (MixedFrames.lift_fst p q I I o o' u v a ha hb)
  have h₂ : MixedFrames.snd p q I I o o' (z default) = v default :=
    congrArg (fun f : Spec (.of K) ⟶ source p q I o' ↦ f default)
      (MixedFrames.lift_snd p q I I o o' u v a ha hb)
  change (MixedFrames.fst p q I I o o' (z default) ∈
    completeInterior (p := p) (q := q) I o) =
    (MixedFrames.snd p q I I o o' (z default) ∈
      completeInterior (p := p) (q := q) I o') at H
  rw [h₁, h₂] at H
  exact H.to_iff

/-- Finite geometry of one original endpoint reaches an independently prescribed frame. -/
theorem fixed_frame_interior_of_finite_endpoint (hu : Complete I o u)
    (hf : (u ≫ first p q I o) default ∈ finiteTargetOpen p) :
    v default ∈ completeInterior (p := p) (q := q) I o' := by
  apply (mixed_original_arrow_interior_iff e I o o' u v a ha hb).mp
  exact complete_mem_interior_of_finiteTarget I o (u default)
    ((complete_iff_mem_completePointLocus I o u).mp hu) hf

end FLT.Mazur.EquivalenceRelationNormalizedFrames
