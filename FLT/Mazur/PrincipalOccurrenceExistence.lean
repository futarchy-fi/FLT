/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceStages
public import FLT.Mazur.FiniteTypePrincipalFiniteMaps

/-!
# Constructing shared occurrence stages

Group all incoming occurrences by target before lifting their coordinate
maps. This constructs one actual target relation set for every overlap,
without duplicating targets or identifying independently chosen stages.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e)))

/-- Incoming occurrences are the fiber of the target function on all edges. -/
abbrev PrincipalIncoming (j : κ) := {e : Σ i, J i // dst e.1 e.2 = j}

/-- View a coordinate map as an incoming map into its specified target. -/
def principalIncomingMap (j : κ) (e : PrincipalIncoming (dst := dst) j) :
    Localization.Away (a e.val.1 e.val.2) →ₐ[R] Localization.Away (b j) := by
  obtain ⟨⟨i, k⟩, rfl⟩ := e
  exact f i k

variable [Finite ι] [∀ i, Finite (J i)]

/-- Lift all maps with prescribed shared source stages and arbitrary target lower bounds. -/
theorem exists_principalOccurrenceStage
    (s : ∀ i, Finset (relationIdeal R (A i))) (t : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ x : PrincipalOccurrenceStage dst a b f, x.source = s ∧ t ≤ x.target := by
  choose q hq g hg using fun j ↦ exists_principalStageMap_finite_lift (b j)
    (fun e : PrincipalIncoming (dst := dst) j ↦ A e.val.1)
    (fun e ↦ a e.val.1 e.val.2) (principalIncomingMap f j)
    (fun e ↦ s e.val.1) (t j)
  refine ⟨⟨s, q, fun i e ↦ g (dst i e) ⟨⟨i, e⟩, rfl⟩, ?_⟩, rfl, hq⟩
  intro i e
  exact hg (dst i e) ⟨⟨i, e⟩, rfl⟩

/-- The occurrence index has a stage even when some overlaps have no incoming maps. -/
instance principalOccurrenceStageNonempty : Nonempty (PrincipalOccurrenceStage dst a b f) := by
  obtain ⟨x, _, _⟩ := exists_principalOccurrenceStage f (fun _ ↦ ∅) (fun _ ↦ ∅)
  exact ⟨x⟩

end FLT.Mazur.FiniteTypeRelationModel
