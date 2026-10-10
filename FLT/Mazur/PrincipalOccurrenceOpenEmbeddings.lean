/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCoordinateChanges
public import FLT.Mazur.PrincipalFanIntersections

/-!
# Shared overlap schemes embedded in all incoming charts

A single finite overlap target embeds into every incident ambient chart.
Its image is the specified principal open, and products of denominators
compute actual pullbacks of any two such embeddings into the same chart.
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

/-- The occurrence denominator in its shared ambient chart stage. -/
abbrev principalOccurrenceDenominator (i : ι) (e : J i) : Stage R (A i) (x.source i) :=
  Ideal.Quotient.mk _ (principalRepresentative R (A i) (a i e))

/-- The one overlap target has its actual scheme isomorphism to each incident principal open. -/
def principalOccurrenceStageIso (i : ι) (e : J i) :
    Spec (.of (PrincipalStage R (B (dst i e)) (b (dst i e)) (x.target (dst i e)))) ≅
      Spec (.of (PrincipalStage R (A i) (a i e) (x.source i))) :=
  Scheme.Spec.mapIso ((AlgEquiv.ofBijective (x.hom i e) (hx i e)).toRingEquiv.toCommRingCatIso.op)

/-- Embed the shared overlap target into one incident ambient chart. -/
def principalOccurrenceOpen (i : ι) (e : J i) :
    Spec (.of (PrincipalStage R (B (dst i e)) (b (dst i e)) (x.target (dst i e)))) ⟶
      Spec (.of (Stage R (A i) (x.source i))) :=
  (principalOccurrenceStageIso x hx i e).hom ≫
    PrincipalLocalizationSquare.inclusion (principalOccurrenceDenominator x i e)

/-- Every occurrence is an actual open immersion of its shared overlap scheme. -/
instance principalOccurrenceOpen_isOpenImmersion (i : ι) (e : J i) :
    IsOpenImmersion (principalOccurrenceOpen x hx i e) := by
  dsimp only [principalOccurrenceOpen]
  infer_instance

/-- The image is exactly the chosen basic open in the ambient chart stage. -/
theorem principalOccurrenceOpen_opensRange (i : ι) (e : J i) :
    (principalOccurrenceOpen x hx i e).opensRange =
      PrimeSpectrum.basicOpen (principalOccurrenceDenominator x i e) := by
  dsimp only [principalOccurrenceOpen]
  rw [Scheme.Hom.opensRange_comp_of_isIso, PrincipalLocalizationSquare.inclusion_opensRange]

/-- A smaller principal open restricts into the shared overlap target in its chosen coordinates. -/
def principalOccurrenceRestriction (i : ι) (e : J i) {r : Stage R (A i) (x.source i)}
    (h : PrimeSpectrum.basicOpen r ≤
      PrimeSpectrum.basicOpen (principalOccurrenceDenominator x i e)) :
    Spec (.of (Localization.Away r)) ⟶
      Spec (.of (PrincipalStage R (B (dst i e)) (b (dst i e)) (x.target (dst i e)))) :=
  PrincipalLocalizationSquare.openInclusion h ≫ (principalOccurrenceStageIso x hx i e).inv

/-- The restriction has its specified map to the common ambient chart. -/
@[reassoc (attr := simp)] theorem principalOccurrenceRestriction_fac
    (i : ι) (e : J i) {r : Stage R (A i) (x.source i)}
    (h : PrimeSpectrum.basicOpen r ≤
      PrimeSpectrum.basicOpen (principalOccurrenceDenominator x i e)) :
    principalOccurrenceRestriction x hx i e h ≫ principalOccurrenceOpen x hx i e =
      PrincipalLocalizationSquare.inclusion r := by
  dsimp only [principalOccurrenceRestriction, principalOccurrenceOpen]
  rw [Category.assoc, Iso.inv_hom_id_assoc, PrincipalLocalizationSquare.openInclusion_fac]

/-- Shared target embeddings have the actual principal-product intersection in each source chart. -/
theorem principalOccurrenceIntersection_isPullback (i : ι) (e d : J i) :
    IsPullback
      (principalOccurrenceRestriction x hx i e (PrimeSpectrum.basicOpen_mul_le_left
        (principalOccurrenceDenominator x i e) (principalOccurrenceDenominator x i d)))
      (principalOccurrenceRestriction x hx i d (PrimeSpectrum.basicOpen_mul_le_right
        (principalOccurrenceDenominator x i e) (principalOccurrenceDenominator x i d)))
      (principalOccurrenceOpen x hx i e) (principalOccurrenceOpen x hx i d) :=
  principalProduct_isPullback_of_isos _ _
    (principalOccurrenceStageIso x hx i e) (principalOccurrenceStageIso x hx i d)

end FLT.Mazur.FiniteTypeRelationModel
