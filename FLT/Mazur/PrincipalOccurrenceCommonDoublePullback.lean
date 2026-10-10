/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonUnion
public import FLT.Mazur.OpenImmersionImageUnionPullback
/-!
# Literal double patches for canonical common unions

The native double-principal patch is isomorphic to the actual ambient
pullback of any two common occurrences, retaining both chart routes.
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



variable (i t r : ι) (p : PrincipalOccurrenceCommon dst i t)
  (q : PrincipalOccurrenceCommon dst i r)

/-- The actual double-principal patch underlying two common occurrences. -/
abbrev principalOccurrenceCommonDoublePatch : PrincipalOccurrencePatch (dst := dst) p.1 :=
  ⟨⟨⟨i, p.2.1.val⟩, p.2.1.property⟩, q.2.1.val⟩

/-- The double-principal model is the full ambient pullback of the two literal overlaps. -/
def principalOccurrenceCommonDoubleIso :
    principalOccurrencePatchScheme x (principalOccurrenceCommonDoublePatch i t r p q) ≅
      pullback (principalOccurrenceCommonLeft e x hx i t p)
        (principalOccurrenceCommonLeft e x hx i r q) := by
  obtain ⟨j, ⟨k, hk⟩, ⟨l, hl⟩⟩ := p
  obtain ⟨j', ⟨k', hk'⟩, ⟨l', hl'⟩⟩ := q
  subst j
  subst j'
  exact (principalOccurrencePatch_isPullback x hx i k k').isoPullback

/-- The isomorphism retains the first literal overlap map. -/
@[reassoc] theorem principalOccurrenceCommonDoubleIso_fst :
    (principalOccurrenceCommonDoubleIso e x hx i t r p q).hom ≫ pullback.fst _ _ =
      principalOccurrencePatchOpen x hx (principalOccurrenceCommonDoublePatch i t r p q) := by
  obtain ⟨j, ⟨k, hk⟩, ⟨l, hl⟩⟩ := p
  obtain ⟨j', ⟨k', hk'⟩, ⟨l', hl'⟩⟩ := q
  subst j
  subst j'
  exact (principalOccurrencePatch_isPullback x hx i k k').isoPullback_hom_fst

/-- The isomorphism retains the actual outer route into the third chart. -/
@[reassoc] theorem principalOccurrenceCommonDoubleIso_snd_right :
    (principalOccurrenceCommonDoubleIso e x hx i t r p q).hom ≫
        pullback.snd _ _ ≫ principalOccurrenceCommonRight e x hx i r q =
      principalOccurrencePatchOther x hx (principalOccurrenceCommonDoublePatch i t r p q) ≫
        principalOccurrenceOpenAt e x hx r q.2.2.val
          (q.2.2.property.trans q.2.1.property.symm) := by
  obtain ⟨j, ⟨k, hk⟩, ⟨l, hl⟩⟩ := p
  obtain ⟨j', ⟨k', hk'⟩, ⟨l', hl'⟩⟩ := q
  subst j
  subst j'
  exact (principalOccurrencePatch_isPullback x hx i k k').isoPullback_hom_snd_assoc _

end FLT.Mazur.FiniteTypeRelationModel
