/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceActualAtlasEquations
public import FLT.Mazur.PrincipalOccurrenceAtlasCoverEquations

/-!
# Prescribed covers and actual refined atlas routes

One bijective occurrence stage has the prescribed finite patch covers and
all actual cross-chart equations on its full ambient chart rings.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalOccurrenceLocalComparisonLeft
  principalOccurrenceLocalComparisonRight principalOccurrenceCrossEquationTransport

universe u v w z z' z''

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))




variable [Finite ι] [Finite κ] [∀ i, Finite (J i)]
  {ν : κ → Type z'} [∀ j, Finite (ν j)]
  {μ : κ → Type z''} [∀ j, Finite (μ j)]
  (c : ∀ j, μ j → PrincipalOccurrencePatch (dst := dst) j)
  (hc : ∀ j, (⨆ m, (principalOccurrenceOriginalPatchOpen e (c j m)).opensRange) = ⊤)
  (p q : ∀ j, ν j → PrincipalOccurrencePatch (dst := dst) j)
  (i : ∀ j, ν j → ι) (k l : ∀ j n, J (i j n))
  (hk : ∀ j n, dst (i j n) (k j n) = dst (p j n).1.val.1 (p j n).2)
  (hl : ∀ j n, dst (i j n) (l j n) = dst (q j n).1.val.1 (q j n).2)
  {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))
  [∀ i, Mono (U i)]

include hc hUV in
/-- One final stage has both the prescribed covers and equality of the actual refined routes. -/
theorem exists_principalOccurrence_actual_covers_routes
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
          (∀ j, (⨆ m, (principalOccurrencePatchOpen y hy (c j m)).opensRange) = ⊤) ∧
          ∀ j n,
            principalOccurrenceCrossOuterLeft y hy (p j n) (q j n) ≫
                principalOccurrenceOpenAt e y hy (i j n) (k j n) (hk j n) =
              principalOccurrenceCrossOuterRight y hy (p j n) (q j n) ≫
                principalOccurrenceOpenAt e y hy (i j n) (l j n) (hl j n) := by
  obtain ⟨y, hxy, hs, hy, hcy⟩ := exists_principalOccurrence_patch_covers e x c hc s
  obtain ⟨z, hyz, _, hz, he⟩ :=
    exists_principalOccurrence_actual_atlas_routes e y hy p q i k l hk hl U V hUV y.source
  exact ⟨z, hxy.trans hyz,
    fun i ↦ (hs i).trans (principalOccurrence_source_mono hyz i), hz,
    fun j ↦ principalOccurrencePatchCover_of_le e y hy hyz hz (c j) (hcy j), he⟩

end FLT.Mazur.FiniteTypeRelationModel
