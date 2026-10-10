/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonFamily
public import FLT.Mazur.PrincipalOccurrenceAmbientUnion
public import FLT.Mazur.OpenImmersionImageUnionReindex

/-!
# Canonical symmetric unions of common occurrences

Using every common occurrence makes reversal a reindexing of the same
literal overlap schemes. Exhaustive equations give the actual union isomorphism.
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

/-- The first ambient embedding of a common literal overlap. -/
def principalOccurrenceCommonLeft (i t : ι) (p : PrincipalOccurrenceCommon dst i t) :=
  principalOccurrenceOpenAt e x hx i p.2.1.val p.2.1.property

/-- The second ambient embedding of the same literal overlap. -/
def principalOccurrenceCommonRight (i t : ι) (p : PrincipalOccurrenceCommon dst i t) :=
  principalOccurrenceOpenAt e x hx t p.2.2.val p.2.2.property

/-- Common left embeddings remain open immersions. -/
instance principalOccurrenceCommonLeft_isOpenImmersion (i t : ι)
    (p : PrincipalOccurrenceCommon dst i t) :
    IsOpenImmersion (principalOccurrenceCommonLeft e x hx i t p) :=
  principalOccurrenceOpenAt_isOpenImmersion e x hx _ _ _

/-- Common right embeddings remain open immersions. -/
instance principalOccurrenceCommonRight_isOpenImmersion (i t : ι)
    (p : PrincipalOccurrenceCommon dst i t) :
    IsOpenImmersion (principalOccurrenceCommonRight e x hx i t p) :=
  principalOccurrenceOpenAt_isOpenImmersion e x hx _ _ _

/-- The canonical common union in the first ambient chart. -/
def principalOccurrenceCommonUnion (i t : ι) :=
  openImageUnion (principalOccurrenceCommonLeft e x hx i t)

/-- The right presentation is exactly the canonical union for the reversed pair. -/
theorem principalOccurrenceCommonUnion_reverse (i t : ι) :
    openImageUnion (principalOccurrenceCommonRight e x hx i t) =
      principalOccurrenceCommonUnion e x hx t i :=
  openImageUnion_reindex (principalOccurrenceCommonLeft e x hx t i)
    (principalOccurrenceCommonSwap dst i t)

variable
  (he : ∀ j (p q : PrincipalOccurrencePatch (dst := dst) j)
    (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl)

/-- Canonical symmetric pair unions are isomorphic using the actual common overlaps. -/
def principalOccurrenceCommonUnionIso (i t : ι) :
    (principalOccurrenceCommonUnion e x hx i t).toScheme ≅
      (principalOccurrenceCommonUnion e x hx t i).toScheme :=
  principalOccurrenceAmbientUnionIso e x hx he
      (fun p : PrincipalOccurrenceCommon dst i t ↦ p.1) i t
      (fun p ↦ p.2.1.val) (fun p ↦ p.2.2.val)
      (fun p ↦ p.2.1.property) (fun p ↦ p.2.2.property) ≪≫
    openImageUnionReindexIso (principalOccurrenceCommonLeft e x hx t i)
      (principalOccurrenceCommonSwap dst i t)

/-- The canonical comparison retains each common source and swaps its two occurrences. -/
@[reassoc] theorem principalOccurrenceCommonUnionIso_fac (i t : ι)
    (p : PrincipalOccurrenceCommon dst i t) :
    openImageUnionMap (principalOccurrenceCommonLeft e x hx i t) p ≫
        (principalOccurrenceCommonUnionIso e x hx he i t).hom =
      openImageUnionMap (principalOccurrenceCommonLeft e x hx t i)
        (principalOccurrenceCommonSwap dst i t p) := by
  exact (principalOccurrenceAmbientUnionIso_fac_assoc e x hx he
    (fun q : PrincipalOccurrenceCommon dst i t ↦ q.1) i t
    (fun q ↦ q.2.1.val) (fun q ↦ q.2.2.val)
    (fun q ↦ q.2.1.property) (fun q ↦ q.2.2.property) p _).trans
      (openImageUnionReindexIso_fac (principalOccurrenceCommonLeft e x hx t i)
        (principalOccurrenceCommonSwap dst i t) p)

end FLT.Mazur.FiniteTypeRelationModel
