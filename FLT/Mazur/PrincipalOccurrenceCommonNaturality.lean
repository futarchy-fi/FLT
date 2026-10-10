/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonTransition

/-!
# Naturality of the canonical pair comparison

The two routes around the refinement square agree on every literal
common overlap, hence on the whole common union.
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

variable
  (he : ∀ j (p q : PrincipalOccurrencePatch (dst := dst) j)
    (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl)

variable
  (hey : ∀ j (p q : PrincipalOccurrencePatch (dst := dst) j)
    (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
    principalOccurrenceCrossOuterLeft y hy p q ≫ principalOccurrenceOpenAt e y hy i k hk =
      principalOccurrenceCrossOuterRight y hy p q ≫ principalOccurrenceOpenAt e y hy i l hl)

/-- The full pair-comparison square commutes under every bijective refinement. -/
@[reassoc] theorem principalOccurrenceCommonTransition_comparison (i t : ι) :
    principalOccurrenceCommonTransition e x hx hxy hy i t ≫
        (principalOccurrenceCommonUnionIso e x hx he i t).hom =
      (principalOccurrenceCommonUnionIso e y hy hey i t).hom ≫
        principalOccurrenceCommonTransition e x hx hxy hy t i := by
  apply openImageUnion_hom_ext (principalOccurrenceCommonLeft e y hy i t)
  intro p
  have h₁ := congrArg (fun k ↦ k ≫ (principalOccurrenceCommonUnionIso e x hx he i t).hom)
    (principalOccurrenceCommonTransition_component e x hx hxy hy i t p)
  have h₂ := congrArg (fun k ↦ principalOccurrenceOverlapTransition hxy p.1 ≫ k)
    (principalOccurrenceCommonUnionIso_fac e x hx he i t p)
  have h₃ := principalOccurrenceCommonTransition_component e x hx hxy hy t i
    (principalOccurrenceCommonSwap dst i t p)
  have h₄ := congrArg (fun k ↦ k ≫ principalOccurrenceCommonTransition e x hx hxy hy t i)
    (principalOccurrenceCommonUnionIso_fac e y hy hey i t p)
  exact (Category.assoc _ _ _).symm.trans (h₁.trans ((Category.assoc _ _ _).trans
    (h₂.trans (h₃.symm.trans (h₄.symm.trans (Category.assoc _ _ _))))))

end FLT.Mazur.FiniteTypeRelationModel
