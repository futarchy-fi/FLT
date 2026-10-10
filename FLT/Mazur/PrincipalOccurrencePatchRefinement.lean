/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrencePatchCoordinates

/-!
# Refinement and recovery of cross-chart patch coordinates

The actual patch denominator transports through every occurrence refinement
and recovers the prescribed original coordinate. Consequently the patch
images pull back exactly along shared-overlap transitions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  {x y : PrincipalOccurrenceStage dst a b f}


/-- Refinement preserves each patch denominator on the literal overlap ring. -/
theorem principalOccurrencePatchDenominator_transition (hxy : x ≤ y) {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalTransition (b j) (principalOccurrence_target_mono hxy j)
      (principalOccurrencePatchDenominator x p) = principalOccurrencePatchDenominator y p := by
  obtain ⟨⟨⟨i, e⟩, rfl⟩, d⟩ := p
  have h := AlgHom.congr_fun (principalOccurrenceAmbientHom_comm hxy i e)
    (principalOccurrenceDenominator x i d)
  simp only [AlgHom.comp_apply, principalOccurrenceDenominator,
    FiniteRelationModel.transition_mk] at h
  exact h.symm

/-- The patch denominator in the original, unapproximated shared overlap. -/
def principalOccurrenceOriginalPatchDenominator {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) : Localization.Away (b j) := by
  obtain ⟨⟨⟨i, e⟩, rfl⟩, d⟩ := p
  exact f i e (algebraMap (A i) (Localization.Away (a i e)) (a i d))

/-- Finite patch coordinates recover the original restriction denominator. -/
theorem principalOccurrencePatchDenominator_recovery
    (x : PrincipalOccurrenceStage dst a b f) {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalStageMap R (B j) (b j) (x.target j) (principalOccurrencePatchDenominator x p) =
      principalOccurrenceOriginalPatchDenominator (f := f) p := by
  obtain ⟨⟨⟨i, e⟩, rfl⟩, d⟩ := p
  have h := AlgHom.congr_fun (principalOccurrenceAmbientHom_fac x i e)
    (principalOccurrenceDenominator x i d)
  simpa only [principalOccurrencePatchDenominator, principalOccurrenceOriginalPatchDenominator,
    AlgHom.comp_apply, principalOccurrenceDenominator, stageMap_mk,
    principalRepresentative_spec, IsScalarTower.toAlgHom_apply] using h

/-- Patch images pull back exactly along the shared-overlap transition. -/
theorem principalOccurrencePatch_preimage (hxy : x ≤ y)
    (hx : ∀ i e, Function.Bijective (x.hom i e))
    (hy : ∀ i e, Function.Bijective (y.hom i e)) {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    Spec.map (CommRingCat.ofHom
        (principalTransition (b j) (principalOccurrence_target_mono hxy j)).toRingHom) ⁻¹ᵁ
      (principalOccurrencePatchOpen x hx p).opensRange =
        (principalOccurrencePatchOpen y hy p).opensRange := by
  rw [principalOccurrencePatch_opensRange, principalOccurrencePatch_opensRange,
    ← principalOccurrencePatchDenominator_transition hxy p]
  exact PrimeSpectrum.comap_basicOpen _ _

end FLT.Mazur.FiniteTypeRelationModel
