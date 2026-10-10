/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceComparisonLocalCoordinates

/-!
# Simultaneous refinement of actual atlas comparison equations

For any finite collection of concrete cross-chart routes, original atlas
incidence proves the quotient equations. One bijective occurrence refinement
makes all transported maps equal in its actual cross-chart coordinate rings.
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



/-- Transport a fixed-denominator equation to the actual refined cross-chart ring. -/
def principalOccurrenceCrossEquationTransport
    {y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)} (hxy : x ≤ y)
    {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceLocalStage e x j
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
      ⟨x.target j, le_refl (x.target j)⟩ →ₐ[R] PrincipalOccurrenceCrossRing y p q :=
  (principalOccurrenceCrossRefinedEquiv x p q hxy).toAlgHom.comp
    (FiniteRelationIterated.transition R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
      (show (⟨x.target j, le_refl (x.target j)⟩ : Set.Ici (x.target j)) ≤
        ⟨y.target j, principalOccurrence_target_mono hxy j⟩ from
          principalOccurrence_target_mono hxy j))

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

include hUV in
/-- Actual atlas comparison equations descend simultaneously, without assumed compatibility. -/
theorem exists_principalOccurrence_atlas_equations
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ hxy : x ≤ y, s ≤ y.source ∧ (∀ i k, Function.Bijective (y.hom i k)) ∧
        ∀ j n,
          (principalOccurrenceCrossEquationTransport e x hxy (p j n) (q j n)).comp
              (principalOccurrenceLocalComparisonLeft e x hx (p j n) (q j n)
                (i j n) (k j n) (hk j n)) =
            (principalOccurrenceCrossEquationTransport e x hxy (p j n) (q j n)).comp
              (principalOccurrenceLocalComparisonRight e x hx (p j n) (q j n)
                (i j n) (l j n) (hl j n)) := by
  obtain ⟨y, hxy, hs, hy, ht, he⟩ := exists_principalOccurrence_cross_equations e x p q
    (fun j n ↦ Stage R (A (i j n)) (x.source (i j n)))
    (fun j ↦ ⟨x.target j, le_refl (x.target j)⟩)
    (fun j n ↦ principalOccurrenceLocalComparisonLeft e x hx (p j n) (q j n)
      (i j n) (k j n) (hk j n))
    (fun j n ↦ principalOccurrenceLocalComparisonRight e x hx (p j n) (q j n)
      (i j n) (l j n) (hl j n))
    (fun j n ↦ principalOccurrenceLocalComparison_quotient e x hx (p j n) (q j n)
      U V hUV (i j n) (k j n) (l j n) (hk j n) (hl j n)) s
  refine ⟨y, hxy, hs, hy, fun j n ↦ ?_⟩
  dsimp only [principalOccurrenceCrossEquationTransport]
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc]
  exact he j n

end FLT.Mazur.FiniteTypeRelationModel
