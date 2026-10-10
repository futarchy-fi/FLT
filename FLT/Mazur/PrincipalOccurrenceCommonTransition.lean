/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonRecovery
public import FLT.Mazur.PrincipalOccurrenceComparisonNaturality

/-!
# Cartesian refinement of canonical common unions

Exact inverse images of occurrence embeddings construct transition maps
on the full common unions, preserving every literal overlap projection.
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
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))

variable {y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)}
  (hxy : x ≤ y) (hy : ∀ i k, Function.Bijective (y.hom i k))

/-- Refinement pulls back each literal occurrence image exactly. -/
theorem principalOccurrenceOpenAt_transition_preimage {j : κ}
    (i : ι) (k : J i) (hk : dst i k = j) :
    principalOccurrenceAmbientTransition hxy i ⁻¹ᵁ
        (principalOccurrenceOpenAt e x hx i k hk).opensRange =
      (principalOccurrenceOpenAt e y hy i k hk).opensRange := by
  subst j
  change principalOccurrenceAmbientTransition hxy i ⁻¹ᵁ
      (principalOccurrenceOpen x hx i k).opensRange =
    (principalOccurrenceOpen y hy i k).opensRange
  rw [principalOccurrenceOpen_opensRange, principalOccurrenceOpen_opensRange]
  rw [show principalOccurrenceAmbientTransition hxy i ⁻¹ᵁ
      PrimeSpectrum.basicOpen (principalOccurrenceDenominator x i k) =
      PrimeSpectrum.basicOpen (FiniteRelationModel.transition R (relationIdeal R (A i))
        (principalOccurrence_source_mono hxy i) (principalOccurrenceDenominator x i k)) from
    PrimeSpectrum.comap_basicOpen _ _]
  congr 1

/-- The entire later common union is the exact inverse image of the earlier one. -/
theorem principalOccurrenceCommonUnion_transition_preimage (i t : ι) :
    principalOccurrenceAmbientTransition hxy i ⁻¹ᵁ
        principalOccurrenceCommonUnion e x hx i t =
      principalOccurrenceCommonUnion e y hy i t :=
  openImageUnion_preimage _ _ _
    (fun p ↦ principalOccurrenceOpenAt_transition_preimage e x hx hxy hy
      i p.2.1.val p.2.1.property)

/-- Refinement on the whole common union, using its exact ambient inverse image. -/
def principalOccurrenceCommonTransition (i t : ι) :
    (principalOccurrenceCommonUnion e y hy i t).toScheme ⟶
      (principalOccurrenceCommonUnion e x hx i t).toScheme :=
  openImageUnionCartesianMap (principalOccurrenceCommonLeft e x hx i t)
    (principalOccurrenceCommonLeft e y hy i t) (principalOccurrenceAmbientTransition hxy i)
    (fun p ↦ principalOccurrenceOpenAt_transition_preimage e x hx hxy hy
      i p.2.1.val p.2.1.property)

/-- The common-union transition retains the ambient chart transition. -/
@[reassoc] theorem principalOccurrenceCommonTransition_fac (i t : ι) :
    principalOccurrenceCommonTransition e x hx hxy hy i t ≫
        (principalOccurrenceCommonUnion e x hx i t).ι =
      (principalOccurrenceCommonUnion e y hy i t).ι ≫
        principalOccurrenceAmbientTransition hxy i :=
  openImageUnionCartesianMap_fac _ _ _ _

/-- The common-union transition square is cartesian over its full ambient chart. -/
theorem principalOccurrenceCommonTransition_isPullback (i t : ι) :
    IsPullback (principalOccurrenceCommonTransition e x hx hxy hy i t)
      (principalOccurrenceCommonUnion e y hy i t).ι
      (principalOccurrenceCommonUnion e x hx i t).ι
      (principalOccurrenceAmbientTransition hxy i) :=
  openImageUnionCartesianMap_isPullback _ _ _ _

/-- Refinement retains the shared transition on each literal common overlap. -/
@[reassoc] theorem principalOccurrenceCommonTransition_component (i t : ι)
    (p : PrincipalOccurrenceCommon dst i t) :
    openImageUnionMap (principalOccurrenceCommonLeft e y hy i t) p ≫
        principalOccurrenceCommonTransition e x hx hxy hy i t =
      principalOccurrenceOverlapTransition hxy p.1 ≫
        openImageUnionMap (principalOccurrenceCommonLeft e x hx i t) p :=
  openImageUnionCartesianMap_component _ _ _ _ p _
    (principalOccurrenceOpenAt_transition e x hx hxy hy i p.2.1.val p.2.1.property)

end FLT.Mazur.FiniteTypeRelationModel
