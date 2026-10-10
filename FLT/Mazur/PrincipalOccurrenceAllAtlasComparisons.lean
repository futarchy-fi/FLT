/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceActualAtlasEquations

/-!
# The exhaustive finite family of atlas comparisons

For a finite occurrence atlas, all admissible pairs of cross-chart routes
form a finite index type. Refining this family imposes every comparison
at once, without choosing a user-supplied comparison list.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalQuotientEquiv
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient
  FiniteRelationIterated.transition FiniteRelationLocalization.transition
  principalOccurrenceCrossRefinedEquiv
  principalOccurrenceLocalComparisonLeft principalOccurrenceLocalComparisonRight

universe u v w z z'

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))



/-- Every pair of patches and pair of incident routes to one common ambient chart. -/
abbrev PrincipalOccurrenceComparisonIndex (j : κ) :=
  Σ p : PrincipalOccurrencePatch (dst := dst) j,
    Σ q : PrincipalOccurrencePatch (dst := dst) j,
      Σ i : ι, {kl : J i × J i //
        dst i kl.1 = dst p.1.val.1 p.2 ∧ dst i kl.2 = dst q.1.val.1 q.2}

variable [Finite ι] [Finite κ] [∀ i, Finite (J i)]

/-- Exhaustive comparison indexing is finite for a finite occurrence atlas. -/
instance principalOccurrenceComparisonIndex_finite (j : κ) :
    Finite (PrincipalOccurrenceComparisonIndex (dst := dst) j) := inferInstance

variable {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))
  [∀ i, Mono (U i)]

include hx hUV in
/-- A single refinement satisfies every admissible actual cross-chart comparison. -/
theorem exists_principalOccurrence_all_atlas_routes
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
          ∀ (j : κ) (p q : PrincipalOccurrencePatch (dst := dst) j)
            (i : ι) (k l : J i)
            (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
            principalOccurrenceCrossOuterLeft y hy p q ≫ principalOccurrenceOpenAt e y hy i k hk =
              principalOccurrenceCrossOuterRight y hy p q ≫
                principalOccurrenceOpenAt e y hy i l hl := by
  obtain ⟨y, hxy, hs, hy, he⟩ := exists_principalOccurrence_actual_atlas_routes e x hx
    (ν := PrincipalOccurrenceComparisonIndex (dst := dst))
    (fun _ n ↦ n.1) (fun _ n ↦ n.2.1) (fun _ n ↦ n.2.2.1)
    (fun _ n ↦ n.2.2.2.val.1) (fun _ n ↦ n.2.2.2.val.2)
    (fun _ n ↦ n.2.2.2.property.1) (fun _ n ↦ n.2.2.2.property.2) U V hUV s
  refine ⟨y, hxy, hs, hy, fun j p q i k l hk hl ↦ ?_⟩
  exact he j ⟨p, q, i, ⟨(k, l), hk, hl⟩⟩

end FLT.Mazur.FiniteTypeRelationModel
