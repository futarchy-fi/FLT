/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceIncidentPatchRoutes

/-!
# Ambient comparisons with arbitrary literal overlap labels

Exhaustive atlas equations give equality on the full ambient pullback
of two occurrences. Both occurrence domains can use explicit shared
labels, making the result symmetric in the two ambient charts.
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


/-- Relabeling an occurrence preserves its open immersion. -/
instance principalOccurrenceOpenAt_isOpenImmersion {j : κ}
    (i : ι) (k : J i) (h : dst i k = j) :
    IsOpenImmersion (principalOccurrenceOpenAt e x hx i k h) := by
  subst j
  exact principalOccurrenceOpen_isOpenImmersion x hx i k

variable
  (he : ∀ j (p q : PrincipalOccurrencePatch (dst := dst) j)
    (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl)

include he in
/-- Literal-label routes agree on the full intersection in either ambient chart. -/
theorem principalOccurrenceOpenAt_ambient_routes {j₁ j₂ : κ}
    (i t : ι) (k l : J i) (r s : J t)
    (hk : dst i k = j₁) (hl : dst i l = j₂)
    (hr : dst t r = j₁) (hs : dst t s = j₂) :
    pullback.fst (principalOccurrenceOpenAt e x hx i k hk)
        (principalOccurrenceOpenAt e x hx i l hl) ≫ principalOccurrenceOpenAt e x hx t r hr =
      pullback.snd (principalOccurrenceOpenAt e x hx i k hk)
        (principalOccurrenceOpenAt e x hx i l hl) ≫ principalOccurrenceOpenAt e x hx t s hs := by
  subst j₁
  subst j₂
  exact principalOccurrence_ambient_routes e x hx t r hr
    (fun p q ↦ he _ p.1 q.1 t p.2.val q.2.val p.2.property q.2.property)
    i k l rfl s hs

end FLT.Mazur.FiniteTypeRelationModel
