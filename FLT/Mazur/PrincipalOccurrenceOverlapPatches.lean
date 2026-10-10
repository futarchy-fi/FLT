/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceRestrictionCoherence

/-!
# Double-open patches inside a literal shared overlap

An incoming occurrence and a second occurrence in its ambient chart give
an open patch of the shared overlap. The ambient chart may vary between
patches, as may the second overlap label.
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
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  (x : PrincipalOccurrenceStage dst a b f) (hx : ∀ i e, Function.Bijective (x.hom i e))

/-- A patch remembers both its incoming occurrence and the other local overlap. -/
abbrev PrincipalOccurrencePatch (j : κ) :=
  Σ e : PrincipalIncoming (dst := dst) j, J e.val.1

/-- The double principal open in the actual ambient chart of a patch. -/
abbrev principalOccurrencePatchScheme {j : κ} (p : PrincipalOccurrencePatch (dst := dst) j) :
    Scheme.{u} :=
  Spec (.of (Localization.Away (principalOccurrenceDenominator x p.1.val.1 p.1.val.2 *
    principalOccurrenceDenominator x p.1.val.1 p.2)))

/-- Map the patch into its literal shared overlap, without a chart-dependent target copy. -/
def principalOccurrencePatchOpen {j : κ} (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrencePatchScheme x p ⟶
      Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) := by
  obtain ⟨⟨⟨i, e⟩, rfl⟩, d⟩ := p
  exact principalOccurrenceRestriction x hx i e (PrimeSpectrum.basicOpen_mul_le_left _ _)

/-- All patches are open subschemes of the shared overlap. -/
instance principalOccurrencePatchOpen_isOpenImmersion {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    IsOpenImmersion (principalOccurrencePatchOpen x hx p) := by
  obtain ⟨⟨⟨i, e⟩, rfl⟩, d⟩ := p
  dsimp only [principalOccurrencePatchOpen]
  infer_instance

/-- The patch also maps to its second, possibly different, overlap label. -/
def principalOccurrencePatchOther {j : κ} (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrencePatchScheme x p ⟶
      Spec (.of (PrincipalStage R (B (dst p.1.val.1 p.2)) (b (dst p.1.val.1 p.2))
        (x.target (dst p.1.val.1 p.2)))) :=
  principalOccurrenceRestriction x hx p.1.val.1 p.2
    (PrimeSpectrum.basicOpen_mul_le_right _ _)

/-- The second map is an open immersion as well. -/
instance principalOccurrencePatchOther_isOpenImmersion {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    IsOpenImmersion (principalOccurrencePatchOther x hx p) := by
  dsimp only [principalOccurrencePatchOther]
  infer_instance

/-- The two overlap labels meet by an actual pullback in the chosen ambient chart. -/
theorem principalOccurrencePatch_isPullback (i : ι) (e d : J i) :
    IsPullback
      (principalOccurrencePatchOpen x hx ⟨⟨⟨i, e⟩, rfl⟩, d⟩)
      (principalOccurrencePatchOther x hx ⟨⟨⟨i, e⟩, rfl⟩, d⟩)
      (principalOccurrenceOpen x hx i e) (principalOccurrenceOpen x hx i d) :=
  principalOccurrenceIntersection_isPullback x hx i e d

end FLT.Mazur.FiniteTypeRelationModel
