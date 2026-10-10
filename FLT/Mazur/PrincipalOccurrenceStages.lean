/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanStages

/-!
# Shared chart stages with occurrence-specific denominators

Each chart has finitely many outgoing occurrences. Several occurrences may
have the same overlap target, even from different charts. Source relations
are shared per chart, target relations per overlap, and denominators may
vary at every source occurrence.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]

/-- Full coordinate data with both chart and overlap relation sets shared. -/
structure PrincipalOccurrenceStage (dst : ∀ i, J i → κ) (a : ∀ i, J i → A i)
    (b : ∀ j, B j)
    (f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))) where
  /-- One ambient relation set at each chart. -/
  source : ∀ i, Finset (relationIdeal R (A i))
  /-- One relation set at each overlap, shared by all incoming occurrences. -/
  target : ∀ j, Finset (relationIdeal R (B j))
  /-- Coordinates on the occurrence-specific principal open. -/
  hom : ∀ i e, PrincipalStage R (A i) (a i e) (source i) →ₐ[R]
    PrincipalStage R (B (dst i e)) (b (dst i e)) (target (dst i e))
  /-- Every occurrence recovers its specified original coordinate map. -/
  fac : ∀ i e, (principalStageMap R (B (dst i e)) (b (dst i e)) (target (dst i e))).comp
    (hom i e) = (f i e).comp (principalStageMap R (A i) (a i e) (source i))

variable {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}

/-- The outgoing fan retains the literal target stage at each occurrence. -/
def principalOccurrenceFan (x : PrincipalOccurrenceStage dst a b f) (i : ι) :
    PrincipalFanStage (a i) (fun e ↦ b (dst i e)) (f i) where
  source := x.source i
  target e := x.target (dst i e)
  hom := x.hom i
  fac := x.fac i

/-- Refinements commute on all full principal rings, with both vertex levels shared. -/
instance principalOccurrenceStagePreorder : Preorder (PrincipalOccurrenceStage dst a b f) where
  le x y := ∃ hs : x.source ≤ y.source, ∃ ht : x.target ≤ y.target,
    ∀ i e, (y.hom i e).comp (principalTransition (a i e) (hs i)) =
      (principalTransition (b (dst i e)) (ht (dst i e))).comp (x.hom i e)
  le_refl x := by
    refine ⟨le_rfl, le_rfl, fun i e ↦ ?_⟩
    simp only [principalTransition_refl, AlgHom.comp_id, AlgHom.id_comp]
  le_trans x y z hxy hyz := by
    obtain ⟨hs, ht, hxy⟩ := hxy
    obtain ⟨hs', ht', hyz⟩ := hyz
    refine ⟨hs.trans hs', ht.trans ht', fun i e ↦ ?_⟩
    rw [← principalTransition_comp (a i e) (hs i) (hs' i), ← AlgHom.comp_assoc, hyz,
      AlgHom.comp_assoc, hxy, ← AlgHom.comp_assoc, principalTransition_comp]

/-- Source relation sets increase under occurrence refinements. -/
theorem principalOccurrence_source_mono {x y : PrincipalOccurrenceStage dst a b f}
    (h : x ≤ y) : x.source ≤ y.source := h.choose

/-- Target relation sets increase even for targets with no incoming occurrence. -/
theorem principalOccurrence_target_mono {x y : PrincipalOccurrenceStage dst a b f}
    (h : x ≤ y) : x.target ≤ y.target := h.choose_spec.choose

/-- The square of each individual occurrence commutes. -/
theorem principalOccurrence_hom_comm {x y : PrincipalOccurrenceStage dst a b f}
    (h : x ≤ y) (i : ι) (e : J i) :
    (y.hom i e).comp (principalTransition (a i e) (principalOccurrence_source_mono h i)) =
      (principalTransition (b (dst i e)) (principalOccurrence_target_mono h (dst i e))).comp
        (x.hom i e) := h.choose_spec.choose_spec i e

/-- Every global occurrence refinement restricts to the corresponding fan refinement. -/
theorem principalOccurrenceFan_mono {x y : PrincipalOccurrenceStage dst a b f}
    (h : x ≤ y) (i : ι) : principalOccurrenceFan x i ≤ principalOccurrenceFan y i := by
  refine ⟨principalOccurrence_source_mono h i, fun e ↦ ?_⟩
  exact ⟨principalOccurrence_source_mono h i,
    principalOccurrence_target_mono h (dst i e), principalOccurrence_hom_comm h i e⟩

end FLT.Mazur.FiniteTypeRelationModel
