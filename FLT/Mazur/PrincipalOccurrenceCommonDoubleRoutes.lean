/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonDoublePullback
/-!
# Ambient routes on literal double pullbacks

The common-union comparisons retain their prescribed ambient maps after
restriction to each literal pairwise pullback and its native principal model.
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

/-- A common component followed by the pair comparison has its literal right ambient map. -/
@[reassoc] theorem principalOccurrenceCommonUnionIso_ambient (i t : ι)
    (p : PrincipalOccurrenceCommon dst i t) :
    openImageUnionMap (principalOccurrenceCommonLeft e x hx i t) p ≫
        (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
        (principalOccurrenceCommonUnion e x hx t i).ι =
      principalOccurrenceCommonRight e x hx i t p :=
  (Category.assoc _ _ _).symm.trans
    ((principalOccurrenceCommonUnionIso_fac_assoc e x hx he i t p _).trans
      (openImageUnionMap_fac (principalOccurrenceCommonLeft e x hx t i)
        (principalOccurrenceCommonSwap dst i t p)))

variable (i t r : ι) (p : PrincipalOccurrenceCommon dst i t)
  (q : PrincipalOccurrenceCommon dst i r)

/-- The full pullback's first ambient route restricts to the literal first chart route. -/
@[reassoc] theorem principalOccurrenceCommonPullbackMap_first :
    openImageUnionPullbackMap (principalOccurrenceCommonLeft e x hx i t)
        (principalOccurrenceCommonLeft e x hx i r) p q ≫ pullback.fst _ _ ≫
        (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
        (principalOccurrenceCommonUnion e x hx t i).ι =
      pullback.fst _ _ ≫ principalOccurrenceCommonRight e x hx i t p :=
  (openImageUnionPullbackMap_fst_assoc _ _ p q _).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun a ↦ pullback.fst _ _ ≫ a)
        (principalOccurrenceCommonUnionIso_ambient e x hx he i t p)))

/-- The second ambient route similarly retains its literal outer occurrence. -/
@[reassoc] theorem principalOccurrenceCommonPullbackMap_second :
    openImageUnionPullbackMap (principalOccurrenceCommonLeft e x hx i t)
        (principalOccurrenceCommonLeft e x hx i r) p q ≫ pullback.snd _ _ ≫
        (principalOccurrenceCommonUnionIso e x hx he i r).hom ≫
        (principalOccurrenceCommonUnion e x hx r i).ι =
      pullback.snd _ _ ≫ principalOccurrenceCommonRight e x hx i r q :=
  (openImageUnionPullbackMap_snd_assoc _ _ p q _).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun a ↦ pullback.snd _ _ ≫ a)
        (principalOccurrenceCommonUnionIso_ambient e x hx he i r q)))

/-- The native double patch retains the first full ambient route. -/
@[reassoc] theorem principalOccurrenceCommonDoubleIso_first :
    (principalOccurrenceCommonDoubleIso e x hx i t r p q).hom ≫
        openImageUnionPullbackMap (principalOccurrenceCommonLeft e x hx i t)
          (principalOccurrenceCommonLeft e x hx i r) p q ≫ pullback.fst _ _ ≫
        (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
        (principalOccurrenceCommonUnion e x hx t i).ι =
      principalOccurrencePatchOpen x hx (principalOccurrenceCommonDoublePatch i t r p q) ≫
        principalOccurrenceCommonRight e x hx i t p :=
  (congrArg (fun a ↦ (principalOccurrenceCommonDoubleIso e x hx i t r p q).hom ≫ a)
    (principalOccurrenceCommonPullbackMap_first e x hx he i t r p q)).trans
    (principalOccurrenceCommonDoubleIso_fst_assoc e x hx i t r p q _)

/-- The native double patch retains the second full ambient route. -/
@[reassoc] theorem principalOccurrenceCommonDoubleIso_second :
    (principalOccurrenceCommonDoubleIso e x hx i t r p q).hom ≫
        openImageUnionPullbackMap (principalOccurrenceCommonLeft e x hx i t)
          (principalOccurrenceCommonLeft e x hx i r) p q ≫ pullback.snd _ _ ≫
        (principalOccurrenceCommonUnionIso e x hx he i r).hom ≫
        (principalOccurrenceCommonUnion e x hx r i).ι =
      principalOccurrencePatchOther x hx (principalOccurrenceCommonDoublePatch i t r p q) ≫
        principalOccurrenceOpenAt e x hx r q.2.2.val
          (q.2.2.property.trans q.2.1.property.symm) :=
  (congrArg (fun a ↦ (principalOccurrenceCommonDoubleIso e x hx i t r p q).hom ≫ a)
    (principalOccurrenceCommonPullbackMap_second e x hx he i t r p q)).trans
    (principalOccurrenceCommonDoubleIso_snd_right e x hx i t r p q)

end FLT.Mazur.FiniteTypeRelationModel
