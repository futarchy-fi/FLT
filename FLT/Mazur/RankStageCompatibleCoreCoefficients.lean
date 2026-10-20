/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreCoefficientTransitions

/-!
# Compatible invariant coefficients at every infinitesimal rank order

Every full invariant coefficient on the initial affine core extends to a
compatible sequence on all higher cores. Compatibility uses the actual
scheme transitions and the entire independent-endpoint equalizers. This is
an infinitesimal sequence, not descent to the unchanged original source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance sequenceOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance sequenceOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance sequenceOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
local notation "C" => rankStageCoreInvariants e n a ha
local notation "ρ" => rankStageCoreRestriction e n a ha

/-- The identity order comparison is the identity on full invariant coefficients. -/
theorem rankStageCoreRestriction_refl (k : ℕ) (s : C k) : ρ (le_refl k) s = s := by
  have ht : rankStageTransition (Over.mk p) n (le_refl k) = 𝟙 _ := by
    apply (cancel_mono (rankThickeningMap (Over.mk p) n k)).mp
    rw [rankStageTransition_map, Category.id_comp]
  have hm : rankStageCoreMap e n a ha (le_refl k) = 𝟙 _ := by
    apply (cancel_mono (rankStageCore e n a ha k).ι).mp
    rw [rankStageCoreMap_inclusion, ht, Category.comp_id, Category.id_comp]
  apply Subtype.ext
  rw [rankStageCoreRestriction_val, hm]
  rfl

variable {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S)
  (hf : p ≫ f = q ≫ f) [IsSeparated f]

attribute [local irreducible] rankStageCore rankStageCoreRestriction rankStageCoreMap
  rankStageFirst rankStageSecond rankThickening

include hf in
/-- Every initial full invariant extends to a sequence compatible at every pair of orders. -/
theorem exists_compatible_rankStageCore_coefficients (z : C 0) :
    ∃ v : ∀ k : ℕ, C k, v 0 = z ∧ ∀ k l (h : k ≤ l), ρ h (v l) = v k := by
  let lift (k : ℕ) (s : C k) : C (k + 1) :=
    (rankStageCoreRestriction_surjective e n a ha f hf (Nat.le_succ k) s).choose
  let v : ∀ k : ℕ, C k := Nat.rec z (fun k s ↦ lift k s)
  have step (k : ℕ) : ρ (Nat.le_succ k) (v (k + 1)) = v k :=
    (rankStageCoreRestriction_surjective e n a ha f hf (Nat.le_succ k) (v k)).choose_spec
  refine ⟨v, rfl, ?_⟩
  intro k l h
  induction l, h using Nat.le_induction with
  | base => exact rankStageCoreRestriction_refl e n a ha k (v k)
  | succ l h ih =>
    rw [← rankStageCoreRestriction_comp e n a ha h (Nat.le_succ l), step]
    exact ih

end FLT.Mazur.EquivalenceRelationOrderedFrames
