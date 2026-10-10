/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceLocalEquationRefinement
public import FLT.Mazur.PrincipalOccurrenceCrossChartCoordinates

/-!
# Descending equations on actual cross-chart intersections

Local equation descent applies simultaneously to cross-chart product
opens. At the resulting bijective stage the compared maps land in the
actual refined intersection coordinate rings, through their proved
localization equivalences.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalQuotientEquiv
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient
  FiniteRelationIterated.transition FiniteRelationLocalization.transition

universe u v w z z' 

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  [Finite ι] [∀ i, Finite (J i)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Finite κ]

variable (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))

/-- Finite cross-chart equations hold at one bijective refinement in the actual local rings. -/
theorem exists_principalOccurrence_cross_equations
    {ν : κ → Type z'} [∀ j, Finite (ν j)]
    (p q : ∀ j, ν j → PrincipalOccurrencePatch (dst := dst) j)
    (T : ∀ j, ν j → Type u) [∀ j n, CommRing (T j n)] [∀ j n, Algebra R (T j n)]
    [∀ j n, Algebra.FiniteType R (T j n)]
    (t : ∀ j, Set.Ici (x.target j))
    (l r : ∀ j n, T j n →ₐ[R] principalOccurrenceLocalStage e x j
      (principalOccurrencePatchDenominator x (p j n) *
        principalOccurrencePatchDenominator x (q j n)) (t j))
    (h : ∀ j n,
      (FiniteRelationIterated.toQuotient R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) (x.target j)
        (principalOccurrencePatchDenominator x (p j n) *
          principalOccurrencePatchDenominator x (q j n)) (t j)).comp (l j n) =
      (FiniteRelationIterated.toQuotient R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) (x.target j)
        (principalOccurrencePatchDenominator x (p j n) *
          principalOccurrencePatchDenominator x (q j n)) (t j)).comp (r j n))
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ hxy : x ≤ y, s ≤ y.source ∧ (∀ i k, Function.Bijective (y.hom i k)) ∧
        ∃ ht : ∀ j, (t j).val ≤ y.target j, ∀ j n,
          (principalOccurrenceCrossRefinedEquiv x (p j n) (q j n) hxy).toAlgHom.comp
            ((FiniteRelationIterated.transition R (relationIdeal R (B j))
              (principalRepresentative R (B j) (b j)) (x.target j)
              (principalOccurrencePatchDenominator x (p j n) *
                principalOccurrencePatchDenominator x (q j n))
              (show t j ≤ ⟨y.target j, principalOccurrence_target_mono hxy j⟩ from ht j)).comp
                (l j n)) =
          (principalOccurrenceCrossRefinedEquiv x (p j n) (q j n) hxy).toAlgHom.comp
            ((FiniteRelationIterated.transition R (relationIdeal R (B j))
              (principalRepresentative R (B j) (b j)) (x.target j)
              (principalOccurrencePatchDenominator x (p j n) *
                principalOccurrencePatchDenominator x (q j n))
              (show t j ≤ ⟨y.target j, principalOccurrence_target_mono hxy j⟩ from ht j)).comp
                (r j n)) := by
  obtain ⟨y, hxy, hs, hy, ht, he⟩ := exists_principalOccurrence_local_equations e x
    (fun j n ↦ principalOccurrencePatchDenominator x (p j n) *
      principalOccurrencePatchDenominator x (q j n)) T t l r h s
  refine ⟨y, hxy, hs, hy, ht, fun j n ↦ ?_⟩
  exact congrArg
    (fun F ↦ (principalOccurrenceCrossRefinedEquiv x (p j n) (q j n) hxy).toAlgHom.comp F)
    (he j n)

end FLT.Mazur.FiniteTypeRelationModel
