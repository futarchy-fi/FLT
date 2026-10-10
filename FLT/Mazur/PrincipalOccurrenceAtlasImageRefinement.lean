/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalImageComparison
public import FLT.Mazur.PrincipalOccurrenceImageInclusions

/-!
# Exhaustive descent of atlas patch image inclusions

All outer-overlap image inclusions form a finite family. Actual atlas
incidence supplies the original patch inclusions, so no separate list of
patch comparisons is requested. They persist above one bijective stage.
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
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  [∀ i, IsOpenImmersion (U i)] [∀ j, IsOpenImmersion (V j)]
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))
  [Finite ι] [Finite κ] [∀ i, Finite (J i)]

include hUV in
/-- All geometric outer-image inclusions become actual patch-image inclusions on one tail. -/
theorem exists_principalOccurrence_atlas_image_inclusions
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧ (∀ i k, Function.Bijective (y.hom i k)) ∧
        ∀ z : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom), y ≤ z →
          ∀ hz : ∀ i k, Function.Bijective (z.hom i k), ∀ j
            (p q : PrincipalOccurrencePatch (dst := dst) j),
            (V (dst p.1.val.1 p.2)).opensRange ≤ (V (dst q.1.val.1 q.2)).opensRange →
              (principalOccurrencePatchOpen z hz p).opensRange ≤
                (principalOccurrencePatchOpen z hz q).opensRange := by
  let ν (j : κ) := {pq : PrincipalOccurrencePatch (dst := dst) j ×
      PrincipalOccurrencePatch (dst := dst) j //
    (V (dst pq.1.1.val.1 pq.1.2)).opensRange ≤ (V (dst pq.2.1.val.1 pq.2.2)).opensRange}
  obtain ⟨y, hxy, hs, hy, hinc⟩ := exists_principalOccurrence_patch_inclusions e x
    (ν := ν) (fun _ pq ↦ pq.val.1) (fun _ pq ↦ pq.val.2)
    (fun _ pq ↦ principalOccurrenceOriginalPatch_image_le e U V hUV
      pq.val.1 pq.val.2 pq.property) s
  exact ⟨y, hxy, hs, hy, fun z hyz hz j p q h ↦ hinc z hyz hz j ⟨(p, q), h⟩⟩

include hUV in
/-- Every pair of opposite routes with the same outer label has equal images on one tail. -/
theorem exists_principalOccurrence_opposite_patch_images
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧ (∀ i k, Function.Bijective (y.hom i k)) ∧
        ∀ z : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom), y ≤ z →
          ∀ hz : ∀ i k, Function.Bijective (z.hom i k), ∀ j
            (p q : PrincipalOccurrencePatch (dst := dst) j),
            dst p.1.val.1 p.2 = dst q.1.val.1 q.2 →
              (principalOccurrencePatchOpen z hz p).opensRange =
                (principalOccurrencePatchOpen z hz q).opensRange := by
  obtain ⟨y, hxy, hs, hy, hinc⟩ := exists_principalOccurrence_atlas_image_inclusions e x U V hUV s
  refine ⟨y, hxy, hs, hy, fun z hyz hz j p q h ↦ le_antisymm ?_ ?_⟩
  · exact hinc z hyz hz j p q (le_of_eq (congrArg (fun k ↦ (V k).opensRange) h))
  · exact hinc z hyz hz j q p (le_of_eq (congrArg (fun k ↦ (V k).opensRange) h.symm))

end FLT.Mazur.FiniteTypeRelationModel
