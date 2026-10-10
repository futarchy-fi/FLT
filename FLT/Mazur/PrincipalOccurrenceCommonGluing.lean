/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonIdentities
public import FLT.Mazur.OpenAtlasTripleGluing
/-!
# Scheme glue data for canonical occurrence unions

The full ambient routes, inverse pair comparisons, and whole diagonals
assemble the actual scheme gluing datum. No cocycle is assumed.
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


variable
  (he : ∀ j (p q : PrincipalOccurrencePatch (dst := dst) j)
    (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl)


variable [Small.{u} ι] (hdiag : ∀ i, principalOccurrenceCommonUnion e x hx i i = ⊤)
  (hr : ∀ i t r : ι,
    ∃ g : pullback (principalOccurrenceCommonUnion e x hx i t).ι
          (principalOccurrenceCommonUnion e x hx i r).ι ⟶
          (principalOccurrenceCommonUnion e x hx t r).toScheme,
      IsOpenImmersion g ∧
        g ≫ (principalOccurrenceCommonUnion e x hx t r).ι =
          pullback.fst _ _ ≫ (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
            (principalOccurrenceCommonUnion e x hx t i).ι ∧
        g ≫ (principalOccurrenceCommonUnionIso e x hx he t r).hom ≫
            (principalOccurrenceCommonUnion e x hx r t).ι =
          pullback.snd _ _ ≫ (principalOccurrenceCommonUnionIso e x hx he i r).hom ≫
            (principalOccurrenceCommonUnion e x hx r i).ι)

/-- Full ambient geometry constructs scheme glue data for the actual finite source charts. -/
def principalOccurrenceCommonGlueData : Scheme.GlueData.{u} :=
  openAtlasTripleGlueData (fun i ↦ Spec (.of (Stage R (A i) (x.source i))))
    (principalOccurrenceCommonUnion e x hx) (principalOccurrenceCommonUnionIso e x hx he)
    (fun i t r ↦ (hr i t r).choose) (fun i t r ↦ (hr i t r).choose_spec.2.1)
    (fun i t r ↦ (hr i t r).choose_spec.2.2)
    (principalOccurrenceCommonUnionIso_comp e x hx he) hdiag
    (principalOccurrenceCommonUnionIso_diagonal e x hx he)

/-- The gluing charts are exactly the finite source spectra. -/
theorem principalOccurrenceCommonGlueData_chart (i : ι) :
    (principalOccurrenceCommonGlueData e x hx he hdiag hr).U (equivShrink ι i) =
      Spec (.of (Stage R (A i) (x.source i))) :=
  congrArg (fun j ↦ Spec (.of (Stage R (A j) (x.source j))))
    ((equivShrink ι).symm_apply_apply i)

/-- The gluing overlaps are exactly the canonical symmetric ambient unions. -/
theorem principalOccurrenceCommonGlueData_overlap (i t : ι) :
    (principalOccurrenceCommonGlueData e x hx he hdiag hr).V (equivShrink ι i, equivShrink ι t) =
      (principalOccurrenceCommonUnion e x hx i t).toScheme :=
  congrArg₂ (fun j k ↦ (principalOccurrenceCommonUnion e x hx j k).toScheme)
    ((equivShrink ι).symm_apply_apply i) ((equivShrink ι).symm_apply_apply t)

end FLT.Mazur.FiniteTypeRelationModel
