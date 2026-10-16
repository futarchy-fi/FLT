/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationInvariantBoundaryAction
public import FLT.Mazur.EquivalenceRelationNormalizedFrameFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Exact boundary invariance and free moving-endpoint transport

The restricted action is Cartesian over the original action, is free on every
nonempty scheme test, and preserves all coefficients equalized by the original
closed relation. These statements do not require complete frames.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
local notation "ρ" => action e I o i z r s hr hs
local notation "τ" => EquivalenceRelationNormalizedFrames.action e I o
local notation "j" => inclusion (p := p) (q := q) I o i
local notation "b" => endpoint (p := p) (q := q) I o i

/-- Exact equivariance, including the original closed ideal, not only its support. -/
@[reassoc] theorem action_inclusion (σ : Equiv.Perm I) :
    (ρ σ).hom ≫ j = j ≫ (τ σ).hom := map_inclusion e I o i z r s hr hs σ

/-- Pulling the original boundary along a moving permutation recovers the same closed scheme. -/
theorem action_isPullback (σ : Equiv.Perm I) :
    IsPullback (ρ σ).hom j j (τ σ).hom :=
  IsPullback.of_horiz_isIso ⟨action_inclusion e I o i z r s hr hs σ⟩

/-- The pulled-back boundary is an actual closed immersion when the original one is closed. -/
instance inclusion_isClosedImmersion [IsClosedImmersion i] : IsClosedImmersion j :=
  inferInstanceAs (IsClosedImmersion (pullback.fst _ _))

/-- Freeness is retained on the entire original closed scheme, including nonreduced tests. -/
theorem action_free {T : Scheme} [Nonempty T]
    (a : T ⟶ boundary (p := p) (q := q) I o i) (σ : Equiv.Perm I)
    (h : a ≫ (ρ σ).hom = a) : σ = 1 := by
  apply EquivalenceRelationNormalizedFrames.action_free e I o (a ≫ j) σ
  have he := congrArg (fun f ↦ f ≫ j) h
  simpa only [Category.assoc, action_inclusion] using he

/-- Closed coefficients are preserved using the actual transition's two moving endpoints. -/
@[reassoc] theorem action_coefficients {S : Scheme} (c : B ⟶ S)
    (hc : r ≫ c = s ≫ c) (σ : Equiv.Perm I) :
    (ρ σ).hom ≫ b ≫ c = b ≫ c := by
  change map e I o i z r s hr hs σ ≫ b ≫ c = _
  rw [← Category.assoc, map_endpoint, Category.assoc, ← hc,
    ← Category.assoc, transition_first]

include hr hs in
/-- A boundary equation factors after moving the first endpoint exactly when it did before. -/
theorem factors_action_iff {T : Scheme} (a : T ⟶ source p q I o) (σ : Equiv.Perm I) :
    (∃ v : T ⟶ boundary (p := p) (q := q) I o i, v ≫ j = a ≫ (τ σ).hom) ↔
      ∃ v : T ⟶ boundary (p := p) (q := q) I o i, v ≫ j = a := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v ≫ (ρ σ).inv, ?_⟩
    apply (cancel_mono (τ σ).hom).mp
    have he : (ρ σ).inv ≫ j ≫ (τ σ).hom = j := by
      rw [← action_inclusion e I o i z r s hr hs σ, Iso.inv_hom_id_assoc]
    calc
      (v ≫ (ρ σ).inv ≫ j) ≫ (τ σ).hom = v ≫ j := by
        simpa only [Category.assoc] using congrArg (fun f ↦ v ≫ f) he
      _ = a ≫ (τ σ).hom := hv
  · rintro ⟨v, rfl⟩
    exact ⟨v ≫ (ρ σ).hom, by rw [Category.assoc, action_inclusion, Category.assoc]⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
