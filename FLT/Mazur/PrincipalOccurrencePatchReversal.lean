/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrencePatchNaturality

/-!
# Reversing double-overlap patches

A double principal open presents the intersection of two literal overlap
labels in one ambient chart. Reversing its two occurrences gives an
isomorphism which exchanges both projections, even when the labels differ.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i k, Localization.Away (a i k) →ₐ[R] Localization.Away (b (dst i k))}
  (x : PrincipalOccurrenceStage dst a b f) (hx : ∀ i k, Function.Bijective (x.hom i k))

/-- The reverse patch starts in the former outer overlap. -/
def principalOccurrenceReversePatch (i : ι) (k l : J i) :
    PrincipalOccurrencePatch (dst := dst) (dst i l) := ⟨⟨⟨i, l⟩, rfl⟩, k⟩

/-- The two ordered double opens are canonically isomorphic over both overlaps. -/
def principalOccurrencePatchReverseIso (i : ι) (k l : J i) :
    principalOccurrencePatchScheme x ⟨⟨⟨i, k⟩, rfl⟩, l⟩ ≅
      principalOccurrencePatchScheme x (principalOccurrenceReversePatch (dst := dst) i k l) :=
  (principalOccurrencePatch_isPullback x hx i k l).isoIsPullback _ _
    (principalOccurrencePatch_isPullback x hx i l k).flip

/-- The reversed first arrow is the original second arrow. -/
@[reassoc] theorem principalOccurrencePatchReverseIso_open (i : ι) (k l : J i) :
    (principalOccurrencePatchReverseIso x hx i k l).hom ≫
        principalOccurrencePatchOpen x hx (principalOccurrenceReversePatch (dst := dst) i k l) =
      principalOccurrencePatchOther x hx ⟨⟨⟨i, k⟩, rfl⟩, l⟩ :=
  (principalOccurrencePatch_isPullback x hx i k l).isoIsPullback_hom_snd _ _
    (principalOccurrencePatch_isPullback x hx i l k).flip

/-- The reversed second arrow is the original first arrow. -/
@[reassoc] theorem principalOccurrencePatchReverseIso_other (i : ι) (k l : J i) :
    (principalOccurrencePatchReverseIso x hx i k l).hom ≫
        principalOccurrencePatchOther x hx (principalOccurrenceReversePatch (dst := dst) i k l) =
      principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, rfl⟩, l⟩ :=
  (principalOccurrencePatch_isPullback x hx i k l).isoIsPullback_hom_fst _ _
    (principalOccurrencePatch_isPullback x hx i l k).flip

/-- Reversing the occurrences twice inverts the actual scheme isomorphism. -/
theorem principalOccurrencePatchReverseIso_symm (i : ι) (k l : J i) :
    (principalOccurrencePatchReverseIso x hx i k l).symm =
      principalOccurrencePatchReverseIso x hx i l k := by
  apply Iso.ext
  apply (cancel_mono (principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, rfl⟩, l⟩)).mp
  change (principalOccurrencePatchReverseIso x hx i k l).inv ≫
      principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, rfl⟩, l⟩ =
    (principalOccurrencePatchReverseIso x hx i l k).hom ≫
      principalOccurrencePatchOpen x hx (principalOccurrenceReversePatch (dst := dst) i l k)
  rw [principalOccurrencePatchReverseIso_open]
  exact (Iso.inv_comp_eq (principalOccurrencePatchReverseIso x hx i k l)).2
    (principalOccurrencePatchReverseIso_other x hx i k l).symm

end FLT.Mazur.FiniteTypeRelationModel
