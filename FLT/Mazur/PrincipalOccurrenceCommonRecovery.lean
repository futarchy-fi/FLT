/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonUnion
public import FLT.Mazur.PrincipalOccurrenceAmbientUnionRecovery
public import FLT.Mazur.OpenImmersionImageUnionCartesian

/-!
# Cartesian recovery of canonical common unions

The original common union is exactly the inverse image of the finite union.
Its canonical map retains every literal occurrence and is a scheme pullback.
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

/-- The original embedding with its literal common-overlap label. -/
def principalOccurrenceOriginalCommonLeft (i t : ι)
    (p : PrincipalOccurrenceCommon dst i t) :=
  principalOccurrenceOriginalOpenAt e i p.2.1.val p.2.1.property

/-- Original common occurrences embed openly in the original ambient chart. -/
instance principalOccurrenceOriginalCommonLeft_isOpenImmersion (i t : ι)
    (p : PrincipalOccurrenceCommon dst i t) :
    IsOpenImmersion (principalOccurrenceOriginalCommonLeft e i t p) :=
  principalOccurrenceOriginalOpenAt_isOpenImmersion e _ _ _

/-- The canonical common union in the original ambient chart. -/
def principalOccurrenceOriginalCommonUnion (i t : ι) :=
  openImageUnion (principalOccurrenceOriginalCommonLeft e i t)

/-- The entire original common union is the exact inverse image of the finite one. -/
theorem principalOccurrenceCommonUnion_preimage (i t : ι) :
    principalOccurrenceAmbientProjection e x i ⁻¹ᵁ principalOccurrenceCommonUnion e x hx i t =
      principalOccurrenceOriginalCommonUnion e i t :=
  principalOccurrenceAmbientUnion_preimage e x hx
    (fun p : PrincipalOccurrenceCommon dst i t ↦ p.1) i
    (fun p ↦ p.2.1.val) (fun p ↦ p.2.1.property)

/-- The ambient projection restricted to the whole canonical common union. -/
def principalOccurrenceCommonProjection (i t : ι) :
    (principalOccurrenceOriginalCommonUnion e i t).toScheme ⟶
      (principalOccurrenceCommonUnion e x hx i t).toScheme :=
  openImageUnionCartesianMap (principalOccurrenceCommonLeft e x hx i t)
    (principalOccurrenceOriginalCommonLeft e i t) (principalOccurrenceAmbientProjection e x i)
    (fun p ↦ principalOccurrenceOpenAt_preimage e x hx i p.2.1.val p.2.1.property)

/-- The restricted projection retains the full ambient projection. -/
@[reassoc] theorem principalOccurrenceCommonProjection_fac (i t : ι) :
    principalOccurrenceCommonProjection e x hx i t ≫
        (principalOccurrenceCommonUnion e x hx i t).ι =
      (principalOccurrenceOriginalCommonUnion e i t).ι ≫
        principalOccurrenceAmbientProjection e x i :=
  openImageUnionCartesianMap_fac _ _ _ _

/-- The square for the whole common union, rather than only its patches, is cartesian. -/
theorem principalOccurrenceCommonProjection_isPullback (i t : ι) :
    IsPullback (principalOccurrenceCommonProjection e x hx i t)
      (principalOccurrenceOriginalCommonUnion e i t).ι
      (principalOccurrenceCommonUnion e x hx i t).ι
      (principalOccurrenceAmbientProjection e x i) :=
  openImageUnionCartesianMap_isPullback _ _ _ _

/-- Every literal common occurrence retains its original overlap projection. -/
@[reassoc] theorem principalOccurrenceCommonProjection_component (i t : ι)
    (p : PrincipalOccurrenceCommon dst i t) :
    openImageUnionMap (principalOccurrenceOriginalCommonLeft e i t) p ≫
        principalOccurrenceCommonProjection e x hx i t =
      principalOccurrenceOverlapProjection e x p.1 ≫
        openImageUnionMap (principalOccurrenceCommonLeft e x hx i t) p :=
  openImageUnionCartesianMap_component _ _ _ _ p _
    (principalOccurrenceOpenAt_recovery e x hx i p.2.1.val p.2.1.property)

end FLT.Mazur.FiniteTypeRelationModel
