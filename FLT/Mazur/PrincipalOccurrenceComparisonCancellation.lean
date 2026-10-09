/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceComparisonNaturality

/-!
# Cancellation of transported atlas equations

Naturality turns transported old-chart equations into equations after the
surjective ambient relation transition. Cancelling that map proves the
actual refined comparison equation on the whole refined ambient ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalQuotientEquiv
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient
  FiniteRelationIterated.transition FiniteRelationLocalization.transition
  principalOccurrenceCrossRefinedEquiv
  principalOccurrenceLocalComparisonLeft principalOccurrenceLocalComparisonRight
  principalOccurrenceCrossComparisonLeftAlg principalOccurrenceCrossComparisonRightAlg
  principalOccurrenceCrossRingTransition principalOccurrenceCrossEquationTransport

universe u v w z z'

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))



variable {y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)}
  (hxy : x ≤ y) {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)

variable (hy : ∀ i k, Function.Bijective (y.hom i k))

/-- The left local equation transport is the naturality square of the actual comparison. -/
theorem principalOccurrenceLocalComparisonLeft_transport (i : ι) (k : J i)
    (hk : dst i k = dst p.1.val.1 p.2) :
    (principalOccurrenceCrossEquationTransport e x hxy p q).comp
        (principalOccurrenceLocalComparisonLeft e x hx p q i k hk) =
      (principalOccurrenceCrossComparisonLeftAlg e y hy p q i k hk).comp
        (FiniteRelationModel.transition R (relationIdeal R (A i))
          (principalOccurrence_source_mono hxy i)) := by
  rw [principalOccurrenceLocalComparisonLeft, ← AlgHom.comp_assoc,
    ← principalOccurrenceCrossRingTransition]
  exact principalOccurrenceCrossComparisonLeftAlg_natural e x hx hxy p q hy i k hk

/-- The right local equation transport is the other actual comparison naturality square. -/
theorem principalOccurrenceLocalComparisonRight_transport (i : ι) (l : J i)
    (hl : dst i l = dst q.1.val.1 q.2) :
    (principalOccurrenceCrossEquationTransport e x hxy p q).comp
        (principalOccurrenceLocalComparisonRight e x hx p q i l hl) =
      (principalOccurrenceCrossComparisonRightAlg e y hy p q i l hl).comp
        (FiniteRelationModel.transition R (relationIdeal R (A i))
          (principalOccurrence_source_mono hxy i)) := by
  rw [principalOccurrenceLocalComparisonRight, ← AlgHom.comp_assoc,
    ← principalOccurrenceCrossRingTransition]
  exact principalOccurrenceCrossComparisonRightAlg_natural e x hx hxy p q hy i l hl

/-- A transported equation implies equality on the entire refined ambient chart ring. -/
theorem principalOccurrenceComparison_eq_of_transport (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2)
    (h : (principalOccurrenceCrossEquationTransport e x hxy p q).comp
        (principalOccurrenceLocalComparisonLeft e x hx p q i k hk) =
      (principalOccurrenceCrossEquationTransport e x hxy p q).comp
        (principalOccurrenceLocalComparisonRight e x hx p q i l hl)) :
    principalOccurrenceCrossComparisonLeftAlg e y hy p q i k hk =
      principalOccurrenceCrossComparisonRightAlg e y hy p q i l hl := by
  apply (AlgHom.cancel_right (FiniteRelationModel.transition_surjective R
    (relationIdeal R (A i)) (principalOccurrence_source_mono hxy i))).mp
  rw [← principalOccurrenceLocalComparisonLeft_transport e x hx hxy p q hy,
    ← principalOccurrenceLocalComparisonRight_transport e x hx hxy p q hy]
  exact h

/-- Equality in actual coordinates is equality of the two full geometric routes. -/
theorem principalOccurrenceComparison_routes_eq (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2)
    (h : principalOccurrenceCrossComparisonLeftAlg e x hx p q i k hk =
      principalOccurrenceCrossComparisonRightAlg e x hx p q i l hl) :
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl := by
  apply (cancel_epi (principalOccurrenceCrossIso x hx p q).inv).mp
  have hs := congrArg (fun f ↦ Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f))) h
  rw [principalOccurrenceCrossComparisonLeftAlg_spec,
    principalOccurrenceCrossComparisonRightAlg_spec] at hs
  exact hs

end FLT.Mazur.FiniteTypeRelationModel
