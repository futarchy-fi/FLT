/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCrossChartIntersections
public import FLT.Mazur.PrincipalOccurrenceAmbientSquares

/-!
# Principal equations for cross-chart occurrence patches

The image of a double-open patch is the basic open of the second ambient
denominator expressed in the shared overlap coordinates. Products of those
expressions describe intersections even when the ambient charts differ.
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
  (x : PrincipalOccurrenceStage dst a b f) (hx : ∀ i e, Function.Bijective (x.hom i e))


/-- The second ambient denominator expressed in the literal overlap ring. -/
def principalOccurrencePatchDenominator {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    PrincipalStage R (B j) (b j) (x.target j) := by
  obtain ⟨⟨⟨i, e⟩, rfl⟩, d⟩ := p
  exact principalOccurrenceAmbientHom x i e (principalOccurrenceDenominator x i d)

/-- A patch is a principal open of the shared overlap, in its actual coordinates. -/
theorem principalOccurrencePatch_opensRange {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    (principalOccurrencePatchOpen x hx p).opensRange =
      PrimeSpectrum.basicOpen (principalOccurrencePatchDenominator x p) := by
  obtain ⟨⟨⟨i, e⟩, rfl⟩, d⟩ := p
  let H := principalOccurrencePatch_isPullback x hx i e d
  have he := Scheme.Hom.opensRange_comp_of_isIso H.isoPullback.hom
    (pullback.fst (principalOccurrenceOpen x hx i e) (principalOccurrenceOpen x hx i d))
  simp only [H.isoPullback_hom_fst] at he
  rw [he, Scheme.Hom.opensRange_pullbackFst, principalOccurrenceOpen_opensRange]
  simp only [principalOccurrenceOpen_eq_spec]
  exact PrimeSpectrum.comap_basicOpen _ _

/-- Cross-chart intersections have a single explicit product denominator. -/
theorem principalOccurrenceCross_basicOpen {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j) :
    (principalOccurrenceCrossOpen x hx p q).opensRange =
      PrimeSpectrum.basicOpen
        (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q) := by
  rw [principalOccurrenceCross_opensRange, principalOccurrencePatch_opensRange,
    principalOccurrencePatch_opensRange, PrimeSpectrum.basicOpen_mul]
  rfl

/-- A patch has its canonical affine principal-open presentation over the shared overlap. -/
def principalOccurrencePatchIso {j : κ} (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrencePatchScheme x p ≅
      Spec (.of (Localization.Away (principalOccurrencePatchDenominator x p))) :=
  IsOpenImmersion.isoOfRangeEq (principalOccurrencePatchOpen x hx p)
    (PrincipalLocalizationSquare.inclusion (principalOccurrencePatchDenominator x p)) (by
      have h : (principalOccurrencePatchOpen x hx p).opensRange =
          (PrincipalLocalizationSquare.inclusion
            (principalOccurrencePatchDenominator x p)).opensRange := by
        rw [principalOccurrencePatch_opensRange, PrincipalLocalizationSquare.inclusion_opensRange]
      exact congrArg SetLike.coe h)


/-- The principal presentation retains the actual patch embedding. -/
@[reassoc (attr := simp)] theorem principalOccurrencePatchIso_fac {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    (principalOccurrencePatchIso x hx p).hom ≫
      PrincipalLocalizationSquare.inclusion (principalOccurrencePatchDenominator x p) =
        principalOccurrencePatchOpen x hx p :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.FiniteTypeRelationModel
