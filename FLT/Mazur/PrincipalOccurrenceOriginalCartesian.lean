/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalCross
public import FLT.Mazur.PrincipalOccurrencePatchRefinement

/-!
# Cartesian recovery of patch and cross-chart domains

Their original images are the basic opens of the recovered denominators.
This proves that both original comparison domains are actual base changes
of the finite domains, including their full scheme structure.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))



/-- The original patch has the expected denominator in the shared original overlap. -/
theorem principalOccurrenceOriginalPatch_opensRange {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    (principalOccurrenceOriginalPatchOpen e p).opensRange = PrimeSpectrum.basicOpen
      (principalOccurrenceOriginalPatchDenominator (f := fun i k ↦ (e i k).toAlgHom) p) := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  let H := principalOccurrenceOriginalPatch_isPullback e i k l
  have he := Scheme.Hom.opensRange_comp_of_isIso H.isoPullback.hom
    (pullback.fst (principalOccurrenceOriginalOpen e i k) (principalOccurrenceOriginalOpen e i l))
  simp only [H.isoPullback_hom_fst] at he
  rw [he, Scheme.Hom.opensRange_pullbackFst, principalOccurrenceOriginalOpen_opensRange]
  rw [principalOccurrenceOriginalOpen_eq_spec]
  exact PrimeSpectrum.comap_basicOpen _ _

/-- The original common intersection has the product denominator in the original overlap. -/
theorem principalOccurrenceOriginalCross_basicOpen {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j) :
    (principalOccurrenceOriginalCrossOpen e p q).opensRange = PrimeSpectrum.basicOpen
      (principalOccurrenceOriginalPatchDenominator (f := fun i k ↦ (e i k).toAlgHom) p *
        principalOccurrenceOriginalPatchDenominator (f := fun i k ↦ (e i k).toAlgHom) q) := by
  dsimp only [principalOccurrenceOriginalCrossOpen]
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_pullbackFst,
    Scheme.Hom.image_preimage_eq_opensRange_inf, principalOccurrenceOriginalPatch_opensRange,
    principalOccurrenceOriginalPatch_opensRange, PrimeSpectrum.basicOpen_mul]
  rfl

variable [∀ i, Algebra.FiniteType R (A i)] [∀ j, Algebra.FiniteType R (B j)]
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))

/-- Original patch images are precisely the preimages of finite patch images. -/
theorem principalOccurrenceOriginalPatch_preimage {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceOverlapProjection e x j ⁻¹ᵁ
        (principalOccurrencePatchOpen x hx p).opensRange =
      (principalOccurrenceOriginalPatchOpen e p).opensRange := by
  rw [principalOccurrencePatch_opensRange, principalOccurrenceOriginalPatch_opensRange,
    ← principalOccurrencePatchDenominator_recovery x p]
  exact PrimeSpectrum.comap_basicOpen _ _

/-- The patch's recovery square is cartesian. -/
theorem principalOccurrenceOriginalPatchProjection_isPullback {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    IsPullback (principalOccurrenceOriginalPatchProjection e x hx p)
      (principalOccurrenceOriginalPatchOpen e p) (principalOccurrencePatchOpen x hx p)
      (principalOccurrenceOverlapProjection e x j) := by
  apply IsOpenImmersion.isPullback
  · exact (principalOccurrenceOriginalPatchProjection_left e x hx p).symm
  · exact principalOccurrenceOriginalPatch_preimage e x hx p

/-- Cross-chart images also pull back exactly to the original scheme. -/
theorem principalOccurrenceOriginalCross_preimage {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceOverlapProjection e x j ⁻¹ᵁ
        (principalOccurrenceCrossOpen x hx p q).opensRange =
      (principalOccurrenceOriginalCrossOpen e p q).opensRange := by
  rw [principalOccurrenceCross_basicOpen, principalOccurrenceOriginalCross_basicOpen,
    ← principalOccurrencePatchDenominator_recovery x p,
    ← principalOccurrencePatchDenominator_recovery x q, ← map_mul]
  exact PrimeSpectrum.comap_basicOpen _ _

/-- The entire original cross-chart domain is recovered by base change. -/
theorem principalOccurrenceOriginalCrossProjection_isPullback {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j) :
    IsPullback (principalOccurrenceOriginalCrossProjection e p q x hx)
      (principalOccurrenceOriginalCrossOpen e p q) (principalOccurrenceCrossOpen x hx p q)
      (principalOccurrenceOverlapProjection e x j) := by
  apply IsOpenImmersion.isPullback
  · exact (principalOccurrenceOriginalCrossProjection_open e p q x hx).symm
  · exact principalOccurrenceOriginalCross_preimage e x hx p q

end FLT.Mazur.FiniteTypeRelationModel
