/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalBipartiteDirected

/-!
# Simultaneous equations at all overlap targets

At each overlap, impose finitely many equations from finite-type test rings.
All equations can be imposed at once without changing any source chart stage.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z t s

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {E : κ → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {src : ∀ j, E j → ι} {a : ∀ i, A i} {b : ∀ j, B j}
  {f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j)}

/-- Extend all overlap targets while keeping the shared chart stages fixed. -/
def principalBipartiteTargetExtension (x : PrincipalBipartiteStage src a b f)
    (q : ∀ j, Finset (relationIdeal R (B j))) (h : x.target ≤ q) :
    PrincipalBipartiteStage src a b f where
  source := x.source
  target := q
  hom j e := (principalTransition (b j) (h j)).comp (x.hom j e)
  fac j e := by rw [← AlgHom.comp_assoc, principalStageMap_transition, x.fac]

/-- Simultaneous target extension is a commuting incidence refinement. -/
theorem principalBipartiteTargetExtension_le (x : PrincipalBipartiteStage src a b f)
    (q : ∀ j, Finset (relationIdeal R (B j))) (h : x.target ≤ q) :
    x ≤ principalBipartiteTargetExtension x q h := by
  refine ⟨le_rfl, fun j ↦ ⟨le_rfl, h j, fun e ↦ ?_⟩⟩
  change ((principalTransition (b j) (h j)).comp (x.hom j e)).comp
      (principalTransition (a (src j e)) (le_refl (x.source (src j e)))) = _
  rw [principalTransition_refl, AlgHom.comp_id]
  rfl

/-- All finite overlap equation families hold after one simultaneous target extension. -/
theorem exists_principalBipartite_target_equations
    (x : PrincipalBipartiteStage src a b f) {K : κ → Type t} [∀ j, Finite (K j)]
    (C : ∀ j, K j → Type s) [∀ j k, CommRing (C j k)] [∀ j k, Algebra R (C j k)]
    [∀ j k, Algebra.FiniteType R (C j k)]
    (g h : ∀ j k, C j k →ₐ[R] PrincipalStage R (B j) (b j) (x.target j))
    (he : ∀ j k, (principalStageMap R (B j) (b j) (x.target j)).comp (g j k) =
      (principalStageMap R (B j) (b j) (x.target j)).comp (h j k)) :
    ∃ (q : ∀ j, Finset (relationIdeal R (B j))) (hq : x.target ≤ q),
      ∀ j k, (principalTransition (b j) (hq j)).comp (g j k) =
        (principalTransition (b j) (hq j)).comp (h j k) := by
  choose q hq hcomm using fun j ↦
    exists_principal_hom_eq_finite (b j) (C j) (x.target j) (g j) (h j) (he j)
  exact ⟨q, hq, hcomm⟩

end FLT.Mazur.FiniteTypeRelationModel
