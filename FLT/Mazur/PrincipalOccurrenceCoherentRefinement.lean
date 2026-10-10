/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceAllAtlasComparisons
public import FLT.Mazur.PrincipalOccurrenceAtlasCoverEquations
public import FLT.Mazur.PrincipalOccurrenceImageInclusions

/-!
# Covers, image inclusions, and every actual atlas equation

Original finite patch covers and image inclusions descend first. Exhaustive
comparison refinement then retains both conditions and proves every actual
cross-chart route equation at one final bijective occurrence stage.
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
  {μ : κ → Type z'} [∀ j, Finite (μ j)]
  {ν : κ → Type z''} [∀ j, Finite (ν j)]
  (c : ∀ j, μ j → PrincipalOccurrencePatch (dst := dst) j)
  (hc : ∀ j, (⨆ m, (principalOccurrenceOriginalPatchOpen e (c j m)).opensRange) = ⊤)
  (p q : ∀ j, ν j → PrincipalOccurrencePatch (dst := dst) j)
  (hi : ∀ j n, (principalOccurrenceOriginalPatchOpen e (p j n)).opensRange ≤
    (principalOccurrenceOriginalPatchOpen e (q j n)).opensRange)
  {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))
  [∀ i, Mono (U i)]

include hc hi hUV in
/-- All supplied geometric conditions and all actual comparisons hold at one common stage. -/
theorem exists_principalOccurrence_coherent_refinement
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
          (∀ j, (⨆ m, (principalOccurrencePatchOpen y hy (c j m)).opensRange) = ⊤) ∧
          (∀ j n, (principalOccurrencePatchOpen y hy (p j n)).opensRange ≤
            (principalOccurrencePatchOpen y hy (q j n)).opensRange) ∧
          ∀ (j : κ) (p q : PrincipalOccurrencePatch (dst := dst) j)
            (i : ι) (k l : J i)
            (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
            principalOccurrenceCrossOuterLeft y hy p q ≫ principalOccurrenceOpenAt e y hy i k hk =
              principalOccurrenceCrossOuterRight y hy p q ≫
                principalOccurrenceOpenAt e y hy i l hl := by
  obtain ⟨y, hxy, hs, _, hiy⟩ := exists_principalOccurrence_patch_inclusions e x p q hi s
  obtain ⟨z, hyz, _, hz, hcz⟩ :=
    exists_principalOccurrence_patch_covers e y c hc y.source
  obtain ⟨w, hzw, _, hw, he⟩ :=
    exists_principalOccurrence_all_atlas_routes e z hz U V hUV z.source
  exact ⟨w, hxy.trans (hyz.trans hzw),
    fun i ↦ (hs i).trans (principalOccurrence_source_mono (hyz.trans hzw) i), hw,
    fun j ↦ principalOccurrencePatchCover_of_le e z hz hzw hw (c j) (hcz j),
    hiy w (hyz.trans hzw) hw, he⟩

end FLT.Mazur.FiniteTypeRelationModel
