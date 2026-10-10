/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrencePatchCartesian

/-!
# Naturality of both arrows from an occurrence patch

The transition defined using the shared overlap also commutes with the
other overlap arrow. Cancellation in the original ambient chart proves
this without assuming any additional comparison equation.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalOccurrencePatchOpen
  FiniteRelationLocalization.transition

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  {x y : PrincipalOccurrenceStage dst a b f}


/-- The ambient chart transition in the occurrence inverse system. -/
abbrev principalOccurrenceAmbientTransition (hxy : x ≤ y) (i : ι) :
    Spec (.of (Stage R (A i) (y.source i))) ⟶
      Spec (.of (Stage R (A i) (x.source i))) :=
  Spec.map (CommRingCat.ofHom (FiniteRelationModel.transition R (relationIdeal R (A i))
    (principalOccurrence_source_mono hxy i)).toRingHom)

variable (hxy : x ≤ y) (hx : ∀ i k, Function.Bijective (x.hom i k))
  (hy : ∀ i k, Function.Bijective (y.hom i k))

/-- Shared overlap transitions commute with the full ambient chart embeddings. -/
@[reassoc] theorem principalOccurrenceOverlapTransition_open (i : ι) (k : J i) :
    principalOccurrenceOverlapTransition hxy (dst i k) ≫ principalOccurrenceOpen x hx i k =
      principalOccurrenceOpen y hy i k ≫ principalOccurrenceAmbientTransition hxy i :=
  principalOccurrenceOpen_comm hx hy hxy i k

/-- Patch transitions retain the second overlap label as well as the shared one. -/
@[reassoc] theorem principalOccurrencePatchTransition_other {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrencePatchTransition hxy hx hy p ≫ principalOccurrencePatchOther x hx p =
      principalOccurrencePatchOther y hy p ≫
        principalOccurrenceOverlapTransition hxy (dst p.1.val.1 p.2) := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  apply (cancel_mono (principalOccurrenceOpen x hx i l)).mp
  rw [Category.assoc, ← (principalOccurrencePatch_isPullback x hx i k l).w,
    ← Category.assoc, principalOccurrencePatchTransition_fac, Category.assoc,
    principalOccurrenceOverlapTransition_open hxy hx hy, ← Category.assoc,
    (principalOccurrencePatch_isPullback y hy i k l).w, Category.assoc,
    Category.assoc, principalOccurrenceOverlapTransition_open hxy hx hy]

end FLT.Mazur.FiniteTypeRelationModel
