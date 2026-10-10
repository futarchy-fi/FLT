/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceComparisonCancellation

/-!
# Actual refined atlas equations

A finite family of original atlas incidences yields a single bijective
refinement where the actual geometric comparison routes agree. Naturality
and surjectivity remove the old ambient coordinate ring from the result.
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



variable [Finite ι] [Finite κ] [∀ i, Finite (J i)]
  {ν : κ → Type z'} [∀ j, Finite (ν j)]
  (p q : ∀ j, ν j → PrincipalOccurrencePatch (dst := dst) j)
  (i : ∀ j, ν j → ι) (k l : ∀ j n, J (i j n))
  (hk : ∀ j n, dst (i j n) (k j n) = dst (p j n).1.val.1 (p j n).2)
  (hl : ∀ j n, dst (i j n) (l j n) = dst (q j n).1.val.1 (q j n).2)
  {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))
  [∀ i, Mono (U i)]

include hx hUV in
/-- All actual comparison maps agree at one refinement, on the full refined ambient rings. -/
theorem exists_principalOccurrence_actual_atlas_equations
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k), ∀ j n,
          principalOccurrenceCrossComparisonLeftAlg e y hy (p j n) (q j n)
              (i j n) (k j n) (hk j n) =
            principalOccurrenceCrossComparisonRightAlg e y hy (p j n) (q j n)
              (i j n) (l j n) (hl j n) := by
  obtain ⟨y, hxy, hs, hy, he⟩ :=
    exists_principalOccurrence_atlas_equations e x hx p q i k l hk hl U V hUV s
  exact ⟨y, hxy, hs, hy, fun j n ↦
    principalOccurrenceComparison_eq_of_transport e x hx hxy (p j n) (q j n) hy
      (i j n) (k j n) (l j n) (hk j n) (hl j n) (he j n)⟩

include hx hUV in
/-- The two actual refined scheme routes agree, even across distinct literal overlap labels. -/
theorem exists_principalOccurrence_actual_atlas_routes
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k), ∀ j n,
          principalOccurrenceCrossOuterLeft y hy (p j n) (q j n) ≫
              principalOccurrenceOpenAt e y hy (i j n) (k j n) (hk j n) =
            principalOccurrenceCrossOuterRight y hy (p j n) (q j n) ≫
              principalOccurrenceOpenAt e y hy (i j n) (l j n) (hl j n) := by
  obtain ⟨y, hxy, hs, hy, he⟩ :=
    exists_principalOccurrence_actual_atlas_equations e x hx p q i k l hk hl U V hUV s
  exact ⟨y, hxy, hs, hy, fun j n ↦
    principalOccurrenceComparison_routes_eq e y hy (p j n) (q j n)
      (i j n) (k j n) (l j n) (hk j n) (hl j n) (he j n)⟩

end FLT.Mazur.FiniteTypeRelationModel
