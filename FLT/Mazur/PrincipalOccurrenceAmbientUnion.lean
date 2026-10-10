/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceAmbientComparisons
public import FLT.Mazur.OpenImmersionImageUnionIsomorphism

/-!
# Isomorphisms of unions of literal ambient overlaps

The exhaustive comparison equations construct inverse maps between the
full image unions in two ambient charts. The domains are the actual shared
overlap schemes; both union maps retain every literal overlap embedding.
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
  {μ : Type*} (j : μ → κ) (i t : ι) (k : μ → J i) (l : μ → J t)
  (hk : ∀ m, dst i (k m) = j m) (hl : ∀ m, dst t (l m) = j m)

/-- The actual overlap schemes identify their entire unions in the two ambient charts. -/
def principalOccurrenceAmbientUnionIso :
    (openImageUnion (fun m ↦ principalOccurrenceOpenAt e x hx i (k m) (hk m))).toScheme ≅
      (openImageUnion (fun m ↦ principalOccurrenceOpenAt e x hx t (l m) (hl m))).toScheme :=
  openImageUnionIso _ _
    (fun m n ↦ principalOccurrenceOpenAt_ambient_routes e x hx he i t
      (k m) (k n) (l m) (l n) (hk m) (hk n) (hl m) (hl n))
    (fun m n ↦ principalOccurrenceOpenAt_ambient_routes e x hx he t i
      (l m) (l n) (k m) (k n) (hl m) (hl n) (hk m) (hk n))

/-- The union isomorphism retains every original finite overlap embedding. -/
@[reassoc] theorem principalOccurrenceAmbientUnionIso_fac (m : μ) :
    openImageUnionMap (fun m ↦ principalOccurrenceOpenAt e x hx i (k m) (hk m)) m ≫
        (principalOccurrenceAmbientUnionIso e x hx he j i t k l hk hl).hom =
      openImageUnionMap (fun m ↦ principalOccurrenceOpenAt e x hx t (l m) (hl m)) m :=
  openImageUnionIso_fac _ _ _ _ m

/-- Exchanging the ambient charts inverts their entire union isomorphism. -/
theorem principalOccurrenceAmbientUnionIso_symm :
    (principalOccurrenceAmbientUnionIso e x hx he j i t k l hk hl).symm =
      principalOccurrenceAmbientUnionIso e x hx he j t i l k hl hk := rfl

end FLT.Mazur.FiniteTypeRelationModel
