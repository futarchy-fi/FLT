/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonDoubleRoutes
public import FLT.Mazur.OpenImmersionImageUnionPullbackLift
/-!
# Full ambient triple routes from literal double patches

The native patch factorizations extend over the entire pullback of the
canonical pair unions. Their comparison equation holds on that full domain.
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


variable (i t r : ι)

/-- Native double-patch routes construct the full ambient triple route and its comparison. -/
theorem exists_principalOccurrenceCommonTriple_route
    (hr : ∀ (p : PrincipalOccurrenceCommon dst i t) (q : PrincipalOccurrenceCommon dst i r),
      ∃ g : principalOccurrencePatchScheme x (principalOccurrenceCommonDoublePatch i t r p q) ⟶
          (principalOccurrenceCommonUnion e x hx t r).toScheme,
        g ≫ (principalOccurrenceCommonUnion e x hx t r).ι =
            principalOccurrencePatchOpen x hx (principalOccurrenceCommonDoublePatch i t r p q) ≫
              principalOccurrenceCommonRight e x hx i t p ∧
          g ≫ (principalOccurrenceCommonUnionIso e x hx he t r).hom ≫
              (principalOccurrenceCommonUnion e x hx r t).ι =
            principalOccurrencePatchOther x hx (principalOccurrenceCommonDoublePatch i t r p q) ≫
              principalOccurrenceOpenAt e x hx r q.2.2.val
                (q.2.2.property.trans q.2.1.property.symm)) :
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
            (principalOccurrenceCommonUnion e x hx r i).ι := by
  let F := principalOccurrenceCommonLeft e x hx i t
  let G := principalOccurrenceCommonLeft e x hx i r
  let a := pullback.fst (openImageUnion F).ι (openImageUnion G).ι ≫
    (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
      (principalOccurrenceCommonUnion e x hx t i).ι
  let ρ := fun p q ↦ (principalOccurrenceCommonDoubleIso e x hx i t r p q).inv ≫
    (hr p q).choose
  have hρ : ∀ p q, ρ p q ≫ (principalOccurrenceCommonUnion e x hx t r).ι =
      openImageUnionPullbackMap F G p q ≫ a := by
    intro p q
    apply (cancel_epi (principalOccurrenceCommonDoubleIso e x hx i t r p q).hom).mp
    calc
      _ = (hr p q).choose ≫ (principalOccurrenceCommonUnion e x hx t r).ι := by
        simp only [ρ, Category.assoc, Iso.hom_inv_id_assoc]
      _ = _ := (hr p q).choose_spec.1.trans
        (principalOccurrenceCommonDoubleIso_first e x hx he i t r p q).symm
  let _ : IsOpenImmersion a := by
    change IsOpenImmersion (pullback.fst (principalOccurrenceCommonUnion e x hx i t).ι
      (principalOccurrenceCommonUnion e x hx i r).ι ≫
        (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
        (principalOccurrenceCommonUnion e x hx t i).ι)
    infer_instance
  let g := openImageUnionPullbackLift F G a (principalOccurrenceCommonUnion e x hx t r) ρ hρ
  refine ⟨g, ?_, openImageUnionPullbackLift_fac F G a _ ρ hρ, ?_⟩
  · exact openImageUnionPullbackLift_isOpenImmersion F G a _ ρ hρ
  · apply openImageUnionPullbackLift_comparison F G a _ ρ hρ
    intro p q
    apply (cancel_epi (principalOccurrenceCommonDoubleIso e x hx i t r p q).hom).mp
    calc
      _ = (hr p q).choose ≫ (principalOccurrenceCommonUnionIso e x hx he t r).hom ≫
          (principalOccurrenceCommonUnion e x hx r t).ι := by
        simp only [ρ, Category.assoc, Iso.hom_inv_id_assoc]
      _ = _ := (hr p q).choose_spec.2.trans
        (principalOccurrenceCommonDoubleIso_second e x hx he i t r p q).symm

end FLT.Mazur.FiniteTypeRelationModel
