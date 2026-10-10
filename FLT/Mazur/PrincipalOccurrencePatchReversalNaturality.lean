/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrencePatchReversal

/-!
# Patch reversal commutes with refinement

The reversed double-overlap isomorphisms are compatible with the actual
cartesian patch transitions. Thus exchanging distinct overlap labels
retains the same map at every later bijective stage.
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
  {x y : PrincipalOccurrenceStage dst a b f}
  (hxy : x ≤ y) (hx : ∀ i k, Function.Bijective (x.hom i k))
  (hy : ∀ i k, Function.Bijective (y.hom i k))

/-- Reversal commutes with refinement on the whole double-open schemes. -/
@[reassoc] theorem principalOccurrencePatchReverseIso_natural (i : ι) (k l : J i) :
    principalOccurrencePatchTransition hxy hx hy ⟨⟨⟨i, k⟩, rfl⟩, l⟩ ≫
        (principalOccurrencePatchReverseIso x hx i k l).hom =
      (principalOccurrencePatchReverseIso y hy i k l).hom ≫
        principalOccurrencePatchTransition hxy hx hy
          (principalOccurrenceReversePatch (dst := dst) i k l) := by
  apply (cancel_mono (principalOccurrencePatchOpen x hx
    (principalOccurrenceReversePatch (dst := dst) i k l))).mp
  rw [Category.assoc, Category.assoc, principalOccurrencePatchReverseIso_open,
    principalOccurrencePatchTransition_other, principalOccurrencePatchTransition_fac,
    principalOccurrencePatchReverseIso_open_assoc]

end FLT.Mazur.FiniteTypeRelationModel
