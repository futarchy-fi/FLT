/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrencePatchRefinement
public import FLT.Mazur.FiniteRelationIteratedStages

/-!
# Affine coordinates for cross-chart comparison domains

The cross-chart pullback is canonically the principal localization at the
product of the two patch denominators. Its finite-stage ring agrees with
the transported old-denominator model used to descend local equations.
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


variable {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)

/-- The actual coordinate ring of the common cross-chart comparison domain. -/
abbrev PrincipalOccurrenceCrossRing := Localization.Away
  (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)

/-- Identify the cross-chart pullback with its explicit affine principal-open model. -/
def principalOccurrenceCrossIso :
    principalOccurrenceCross x hx p q ≅ Spec (.of (PrincipalOccurrenceCrossRing x p q)) :=
  IsOpenImmersion.isoOfRangeEq (principalOccurrenceCrossOpen x hx p q)
    (PrincipalLocalizationSquare.inclusion
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)) (by
      have h : (principalOccurrenceCrossOpen x hx p q).opensRange =
          (PrincipalLocalizationSquare.inclusion
            (principalOccurrencePatchDenominator x p *
              principalOccurrencePatchDenominator x q)).opensRange := by
        rw [principalOccurrenceCross_basicOpen, PrincipalLocalizationSquare.inclusion_opensRange]
      exact congrArg SetLike.coe h)

/-- The affine coordinates retain the actual map to the shared overlap. -/
@[reassoc (attr := simp)] theorem principalOccurrenceCrossIso_fac :
    (principalOccurrenceCrossIso x hx p q).hom ≫
      PrincipalLocalizationSquare.inclusion
        (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q) =
          principalOccurrenceCrossOpen x hx p q :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Cross-chart comparison domains are affine even when their ambient charts differ. -/
instance principalOccurrenceCross_isAffine : IsAffine (principalOccurrenceCross x hx p q) :=
  IsAffine.of_isIso (principalOccurrenceCrossIso x hx p q).hom

variable {y : PrincipalOccurrenceStage dst a b f} (hxy : x ≤ y)

/-- The current cross-chart ring localizes at the transported old product denominator. -/
theorem principalOccurrenceCrossRing_isLocalization :
    IsLocalization.Away (FiniteRelationIterated.denominator R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
      ⟨y.target j, principalOccurrence_target_mono hxy j⟩)
        (PrincipalOccurrenceCrossRing y p q) := by
  change IsLocalization.Away (principalTransition (b j) _
    (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)) _
  rw [map_mul, principalOccurrencePatchDenominator_transition hxy p,
    principalOccurrencePatchDenominator_transition hxy q]
  infer_instance

/-- The equation-descent target is the actual refined cross-chart coordinate ring. -/
def principalOccurrenceCrossRefinedEquiv :
    FiniteRelationIterated.Stage R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
      ⟨y.target j, principalOccurrence_target_mono hxy j⟩ ≃ₐ[R]
        PrincipalOccurrenceCrossRing y p q := by
  let d := FiniteRelationIterated.denominator R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j)
    (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
    ⟨y.target j, principalOccurrence_target_mono hxy j⟩
  let _ := principalOccurrenceCrossRing_isLocalization x p q hxy
  exact (IsLocalization.algEquiv (Submonoid.powers d)
    (Localization.Away d) (PrincipalOccurrenceCrossRing y p q)).restrictScalars R

/-- The refined comparison fixes every numerator in the overlap ring. -/
theorem principalOccurrenceCrossRefinedEquiv_algebraMap
    (z : PrincipalStage R (B j) (b j) (y.target j)) :
    principalOccurrenceCrossRefinedEquiv x p q hxy (algebraMap _ _ z) =
      algebraMap _ (PrincipalOccurrenceCrossRing y p q) z := by
  let d := FiniteRelationIterated.denominator R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j)
    (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
    ⟨y.target j, principalOccurrence_target_mono hxy j⟩
  let _ := principalOccurrenceCrossRing_isLocalization x p q hxy
  exact (IsLocalization.algEquiv (Submonoid.powers d)
    (Localization.Away d) (PrincipalOccurrenceCrossRing y p q)).commutes z

end FLT.Mazur.FiniteTypeRelationModel
