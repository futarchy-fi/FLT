/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonPatchRoutes
public import FLT.Mazur.OpenImmersionImagePullbackCover
/-!
# Comparing covered triple-patch routes

On every cross-patch intersection the constructed union route equals the
literal outer occurrence. Exhaustive equations identify its composite
with the pair comparison on the entire covered patch.
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


/-- The two routes of a labeled patch agree in its ambient chart. -/
@[reassoc] theorem principalOccurrencePatchAt_square {j : κ} (i : ι) (k l : J i)
    (hk : dst i k = j) :
    principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, hk⟩, l⟩ ≫
        principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrencePatchOther x hx ⟨⟨⟨i, k⟩, hk⟩, l⟩ ≫
        principalOccurrenceOpenAt e x hx i l rfl := by
  subst j
  exact (principalOccurrencePatch_isPullback x hx i k l).w

variable {j : κ} (p : PrincipalOccurrencePatch (dst := dst) j)
  (i t : ι) (k : J i) (hk : dst i k = j)
  {μ : Type*} (l : μ → J i) (n : μ → J t) (hn : ∀ m, dst t (n m) = dst i (l m))
  (hc : (principalOccurrencePatchOpen x hx p).opensRange ≤
    ⨆ m, (principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, hk⟩, l m⟩).opensRange)


/-- The route restricts on each covering cross patch to its literal common occurrence. -/
@[reassoc] theorem principalOccurrenceCommonPatchRoute_cross (m : μ) :
    principalOccurrenceCrossLeft x hx p ⟨⟨⟨i, k⟩, hk⟩, l m⟩ ≫
        principalOccurrenceCommonPatchRoute e x hx p i t k hk l n hn hc =
      principalOccurrenceCrossOuterRight x hx p ⟨⟨⟨i, k⟩, hk⟩, l m⟩ ≫
        openImageUnionMap (principalOccurrenceCommonLeft e x hx i t)
          ⟨dst i (l m), ⟨l m, rfl⟩, ⟨n m, hn m⟩⟩ := by
  apply (cancel_mono (principalOccurrenceCommonUnion e x hx i t).ι).mp
  let q : PrincipalOccurrencePatch (dst := dst) j := ⟨⟨⟨i, k⟩, hk⟩, l m⟩
  let c : PrincipalOccurrenceCommon dst i t := ⟨dst i (l m), ⟨l m, rfl⟩, ⟨n m, hn m⟩⟩
  have H : principalOccurrenceCrossLeft x hx p q ≫
      principalOccurrencePatchOpen x hx p ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫
        principalOccurrenceOpenAt e x hx i (l m) rfl := by
    change (pullback.fst _ _) ≫ _ ≫ _ = (pullback.snd _ _ ≫ _) ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc,
      principalOccurrencePatchAt_square, Category.assoc]
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun a ↦ principalOccurrenceCrossLeft x hx p q ≫ a)
      (principalOccurrenceCommonPatchRoute_fac e x hx p i t k hk l n hn hc))).trans
    (H.trans (((Category.assoc _ _ _).trans
      (congrArg (fun a ↦ principalOccurrenceCrossOuterRight x hx p q ≫ a)
        (openImageUnionMap_fac (principalOccurrenceCommonLeft e x hx i t) c))).symm))

variable
  (he : ∀ j (p q : PrincipalOccurrencePatch (dst := dst) j)
    (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl)
  (r : J t) (hr : dst t r = dst p.1.val.1 p.2)

/-- The full covered patch follows the prescribed route into the third chart. -/
@[reassoc] theorem principalOccurrenceCommonPatchRoute_comparison :
    principalOccurrenceCommonPatchRoute e x hx p i t k hk l n hn hc ≫
        (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
        (principalOccurrenceCommonUnion e x hx t i).ι =
      principalOccurrencePatchOther x hx p ≫ principalOccurrenceOpenAt e x hx t r hr := by
  apply openImagePullback_hom_ext (principalOccurrencePatchOpen x hx p)
    (fun m ↦ principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, hk⟩, l m⟩) hc
  intro m
  change principalOccurrenceCrossLeft x hx p _ ≫ _ =
    principalOccurrenceCrossLeft x hx p _ ≫ _
  let q : PrincipalOccurrencePatch (dst := dst) j := ⟨⟨⟨i, k⟩, hk⟩, l m⟩
  let c : PrincipalOccurrenceCommon dst i t := ⟨dst i (l m), ⟨l m, rfl⟩, ⟨n m, hn m⟩⟩
  have H : openImageUnionMap (principalOccurrenceCommonLeft e x hx i t) c ≫
      (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
      (principalOccurrenceCommonUnion e x hx t i).ι =
      principalOccurrenceOpenAt e x hx t (n m) (hn m) :=
    (Category.assoc _ _ _).symm.trans
      ((principalOccurrenceCommonUnionIso_fac_assoc e x hx he i t c _).trans
        (openImageUnionMap_fac (principalOccurrenceCommonLeft e x hx t i)
          (principalOccurrenceCommonSwap dst i t c)))
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun a ↦ a ≫ (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
      (principalOccurrenceCommonUnion e x hx t i).ι)
      (principalOccurrenceCommonPatchRoute_cross e x hx p i t k hk l n hn hc m)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a ↦ principalOccurrenceCrossOuterRight x hx p q ≫ a) H).trans
        ((he j p q t r (n m) hr (hn m)).symm.trans (Category.assoc _ _ _))))))

end FLT.Mazur.FiniteTypeRelationModel
