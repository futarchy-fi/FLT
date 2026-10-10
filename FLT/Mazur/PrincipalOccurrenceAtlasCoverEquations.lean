/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceAtlasEquationRefinement
public import FLT.Mazur.PrincipalOccurrenceCoverRefinement
public import FLT.Mazur.PrincipalOccurrencePatchCartesian

/-!
# Prescribed covers and actual atlas equations at a common stage

Covers persist through every occurrence refinement. First descend the
prescribed original patch covers, then descend the concrete atlas equations
above that stage, preserving the covers at the final bijective stage.
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




/-- A patch subfamily remains a cover under every bijective occurrence refinement. -/
theorem principalOccurrencePatchCover_of_le
    {y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)} (hxy : x ≤ y)
    (hy : ∀ i k, Function.Bijective (y.hom i k)) {j : κ} {μ : Type*}
    (c : μ → PrincipalOccurrencePatch (dst := dst) j)
    (hc : (⨆ m, (principalOccurrencePatchOpen x hx (c m)).opensRange) = ⊤) :
    (⨆ m, (principalOccurrencePatchOpen y hy (c m)).opensRange) = ⊤ := by
  have h := congrArg (fun W ↦ principalOccurrenceOverlapTransition hxy j ⁻¹ᵁ W) hc
  simpa only [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_top,
    principalOccurrencePatch_preimage hxy hx hy] using h

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
/-- Prescribed original covers and concrete atlas equations hold at one final bijective stage. -/
theorem exists_principalOccurrence_atlas_covers_equations
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
        ∃ z : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
          ∃ hyz : y ≤ z, ∃ hz : ∀ i k, Function.Bijective (z.hom i k),
            s ≤ z.source ∧
              (∀ j, (⨆ m, (principalOccurrencePatchOpen z hz (c j m)).opensRange) = ⊤) ∧
              ∀ j n,
                (principalOccurrenceCrossEquationTransport e y hyz (p j n) (q j n)).comp
                    (principalOccurrenceLocalComparisonLeft e y hy (p j n) (q j n)
                      (i j n) (k j n) (hk j n)) =
                  (principalOccurrenceCrossEquationTransport e y hyz (p j n) (q j n)).comp
                    (principalOccurrenceLocalComparisonRight e y hy (p j n) (q j n)
                      (i j n) (l j n) (hl j n)) := by
  obtain ⟨y, hxy, hs, hy, hcy⟩ := exists_principalOccurrence_patch_covers e x c hc s
  obtain ⟨z, hyz, _, hz, he⟩ :=
    exists_principalOccurrence_atlas_equations e y hy p q i k l hk hl U V hUV y.source
  exact ⟨y, hxy, hy, z, hyz, hz,
    fun i ↦ (hs i).trans (principalOccurrence_source_mono hyz i),
    fun j ↦ principalOccurrencePatchCover_of_le e y hy hyz hz (c j) (hcy j), he⟩

end FLT.Mazur.FiniteTypeRelationModel
