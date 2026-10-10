/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalBipartiteDirected

/-!
# Shared stages for two successive incidence layers

Charts, double intersections and triple intersections use one relation set
per vertex. The middle stages are shared by incoming and outgoing arrows.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z v' w'

variable {R : Type u} [CommRing R]
  {ι : Type v} {κ : Type w} {τ : Type v'} {E : κ → Type z} {F : τ → Type w'}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {C : τ → Type u} [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
  [∀ k, Algebra.FiniteType R (C k)]

/-- Two incidence layers whose middle stages are shared literally. -/
structure PrincipalLayeredStage (src : ∀ j, E j → ι) (mid : ∀ k, F k → κ)
    (a : ∀ i, A i) (b : ∀ j, B j) (c : ∀ k, C k)
    (f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j))
    (g : ∀ k e, Localization.Away (b (mid k e)) →ₐ[R] Localization.Away (c k)) where
  /-- The chart-to-double-intersection incidence model. -/
  lower : PrincipalBipartiteStage src a b f
  /-- Relation sets at the triple-intersection targets. -/
  target : ∀ k, Finset (relationIdeal R (C k))
  /-- Outgoing maps use precisely the middle stages of the lower layer. -/
  hom : ∀ k e, PrincipalStage R (B (mid k e)) (b (mid k e)) (lower.target (mid k e)) →ₐ[R]
    PrincipalStage R (C k) (c k) (target k)
  /-- Each outgoing map recovers the original coordinate map. -/
  fac : ∀ k e, (principalStageMap R (C k) (c k) (target k)).comp (hom k e) =
    (g k e).comp (principalStageMap R (B (mid k e)) (b (mid k e)) (lower.target (mid k e)))

variable
  {src : ∀ j, E j → ι} {mid : ∀ k, F k → κ}
  {a : ∀ i, A i} {b : ∀ j, B j} {c : ∀ k, C k}
  {f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j)}
  {g : ∀ k e, Localization.Away (b (mid k e)) →ₐ[R] Localization.Away (c k)}

/-- Extract the upper incidence model, with the same middle relation sets. -/
def principalLayeredUpper (x : PrincipalLayeredStage src mid a b c f g) :
    PrincipalBipartiteStage mid b c g where
  source := x.lower.target
  target := x.target
  hom := x.hom
  fac := x.fac

/-- Assemble two layers whose middle relation sets agree. -/
def principalLayeredOfLayers (x : PrincipalBipartiteStage src a b f)
    (y : PrincipalBipartiteStage mid b c g) (h : y.source = x.target) :
    PrincipalLayeredStage src mid a b c f g := by
  rcases y with ⟨s, t, maps, fac⟩
  dsimp at h
  subst s
  exact ⟨x, t, maps, fac⟩

/-- Assembly preserves the lower layer. -/
@[simp] theorem principalLayeredOfLayers_lower (x : PrincipalBipartiteStage src a b f)
    (y : PrincipalBipartiteStage mid b c g) (h : y.source = x.target) :
    (principalLayeredOfLayers x y h).lower = x := by
  cases y
  cases h
  rfl

/-- Assembly preserves the upper layer. -/
@[simp] theorem principalLayeredOfLayers_upper (x : PrincipalBipartiteStage src a b f)
    (y : PrincipalBipartiteStage mid b c g) (h : y.source = x.target) :
    principalLayeredUpper (principalLayeredOfLayers x y h) = y := by
  cases y
  cases h
  rfl

/-- A refinement commutes in both incidence layers. -/
instance principalLayeredStagePreorder : Preorder (PrincipalLayeredStage src mid a b c f g) where
  le x y := x.lower ≤ y.lower ∧ principalLayeredUpper x ≤ principalLayeredUpper y
  le_refl x := ⟨le_rfl, le_rfl⟩
  le_trans x y z hxy hyz := ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

variable [∀ k, Finite (F k)]

/-- Lift the second layer with the first layer fixed and arbitrary final bounds. -/
theorem exists_principalLayeredStage_over (x : PrincipalBipartiteStage src a b f)
    (t : ∀ k, Finset (relationIdeal R (C k))) :
    ∃ y : PrincipalLayeredStage src mid a b c f g, y.lower = x ∧ t ≤ y.target := by
  obtain ⟨z, hz, ht⟩ := exists_principalBipartiteStage (src := mid) (a := b) (b := c)
    (f := g) x.target t
  refine ⟨principalLayeredOfLayers x z hz, principalLayeredOfLayers_lower x z hz, ?_⟩
  change t ≤ (principalLayeredUpper (principalLayeredOfLayers x z hz)).target
  rw [principalLayeredOfLayers_upper]
  exact ht

variable [∀ j, Finite (E j)]

/-- Both layers lift simultaneously beyond arbitrary bounds at all three levels. -/
theorem exists_principalLayeredStage (s : ∀ i, Finset (relationIdeal R (A i)))
    (t : ∀ j, Finset (relationIdeal R (B j))) (q : ∀ k, Finset (relationIdeal R (C k))) :
    ∃ y : PrincipalLayeredStage src mid a b c f g,
      y.lower.source = s ∧ t ≤ y.lower.target ∧ q ≤ y.target := by
  obtain ⟨x, hx, ht⟩ := exists_principalBipartiteStage (src := src) (a := a) (b := b) (f := f) s t
  obtain ⟨y, hy, hq⟩ := exists_principalLayeredStage_over (mid := mid) (c := c) (g := g) x q
  refine ⟨y, ?_, ?_, hq⟩
  · rw [hy]
    exact hx
  · rw [hy]
    exact ht

/-- The combined incidence index has a stage. -/
instance principalLayeredStageNonempty : Nonempty (PrincipalLayeredStage src mid a b c f g) := by
  obtain ⟨x, _, _, _⟩ := exists_principalLayeredStage (src := src) (mid := mid)
    (a := a) (b := b) (c := c) (f := f) (g := g) (fun _ ↦ ∅) (fun _ ↦ ∅) (fun _ ↦ ∅)
  exact ⟨x⟩

end FLT.Mazur.FiniteTypeRelationModel
