/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyDirected

/-!
# Simultaneous chart stages for several overlap targets

An incidence family specifies which source charts map to each target.
Every source chart has one shared relation set, even when it occurs in
several overlaps. Each target has finitely many incoming coordinate maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {E : κ → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]

/-- A finite-stage incidence diagram with source stages shared across targets. -/
structure PrincipalBipartiteStage (src : ∀ j, E j → ι) (a : ∀ i, A i) (b : ∀ j, B j)
    (f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j)) where
  /-- A single relation set for each source chart. -/
  source : ∀ i, Finset (relationIdeal R (A i))
  /-- A relation set for each overlap target. -/
  target : ∀ j, Finset (relationIdeal R (B j))
  /-- Lifted coordinate maps along all incidences. -/
  hom : ∀ j e, PrincipalStage R (A (src j e)) (a (src j e)) (source (src j e)) →ₐ[R]
    PrincipalStage R (B j) (b j) (target j)
  /-- Each incidence map recovers the given original map. -/
  fac : ∀ j e, (principalStageMap R (B j) (b j) (target j)).comp (hom j e) =
    (f j e).comp (principalStageMap R (A (src j e)) (a (src j e)) (source (src j e)))

variable {src : ∀ j, E j → ι} {a : ∀ i, A i} {b : ∀ j, B j}
  {f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j)}

/-- Extract the incoming family at a single overlap target. -/
def principalBipartiteLeg (x : PrincipalBipartiteStage src a b f) (j : κ) :
    PrincipalFamilyStage (fun e ↦ a (src j e)) (b j) (f j) where
  source e := x.source (src j e)
  target := x.target j
  hom := x.hom j
  fac := x.fac j

/-- Refinements increase every chart stage and commute at every overlap target. -/
instance principalBipartiteStagePreorder : Preorder (PrincipalBipartiteStage src a b f) where
  le x y := x.source ≤ y.source ∧ ∀ j, principalBipartiteLeg x j ≤ principalBipartiteLeg y j
  le_refl x := ⟨le_rfl, fun _ ↦ le_rfl⟩
  le_trans x y z hxy hyz := ⟨hxy.1.trans hyz.1, fun j ↦ (hxy.2 j).trans (hyz.2 j)⟩

/-- Every refinement increases each target relation set. -/
theorem principalBipartite_target_mono {x y : PrincipalBipartiteStage src a b f}
    (h : x ≤ y) : x.target ≤ y.target :=
  fun j ↦ (h.2 j).choose_spec.choose

/-- The coordinate square at each incidence commutes under refinement. -/
theorem principalBipartite_hom_comm {x y : PrincipalBipartiteStage src a b f}
    (h : x ≤ y) (j : κ) (e : E j) :
    (y.hom j e).comp (principalTransition (a (src j e)) (h.1 (src j e))) =
      (principalTransition (b j) (principalBipartite_target_mono h j)).comp (x.hom j e) :=
  (h.2 j).choose_spec.choose_spec e

variable [∀ j, Finite (E j)]

/-- All incidence maps lift simultaneously while keeping every source stage fixed. -/
theorem exists_principalBipartiteStage (s : ∀ i, Finset (relationIdeal R (A i)))
    (t : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ x : PrincipalBipartiteStage src a b f, x.source = s ∧ t ≤ x.target := by
  choose q ht g hg using fun j ↦ exists_principalStageMap_finite_lift (b j)
    (fun e ↦ A (src j e)) (fun e ↦ a (src j e)) (f j) (fun e ↦ s (src j e)) (t j)
  exact ⟨⟨s, q, g, hg⟩, rfl, ht⟩

/-- There is an incidence model even before specifying any relation bounds. -/
instance principalBipartiteStageNonempty : Nonempty (PrincipalBipartiteStage src a b f) := by
  obtain ⟨x, _, _⟩ := exists_principalBipartiteStage (src := src) (a := a) (b := b) (f := f)
    (fun _ ↦ ∅) (fun _ ↦ ∅)
  exact ⟨x⟩

end FLT.Mazur.FiniteTypeRelationModel
