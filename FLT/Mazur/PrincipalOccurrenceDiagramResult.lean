/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceDiagramFiniteRestrictions
public import FLT.Mazur.PrincipalOccurrenceStageFromDiagram
public import FLT.Mazur.PrincipalOccurrenceRefinedPaths
public import FLT.Mazur.OccurrenceMixedSourceResult

/-!
# Simultaneous geometric coordinate and restriction refinement

Apply the polynomial occurrence theorem to the actual combined source/overlap
family. Both levels of arrows share one ambient relation set at each chart,
while restrictions retain their earlier source overlap stages in the old squares.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalFanInitialRestrictionEquiv
  principalFanOriginalRestriction principalQuotientEquiv principalFanRestrictionProjection
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))

local notation "C" => PrincipalOccurrenceAmbient A B
local notation "I" => fun i ↦ relationIdeal R (C i)
local notation "r" => principalOccurrenceAmbientRepresentative (R := R) A B a b
local notation "s" => principalOccurrenceAmbientRelations A B x.source x.target


variable (t : ∀ j, Finset (relationIdeal R (B j)))
  (ρ : ∀ i k l, PrincipalStage R (B (dst i k)) (b (dst i k)) (t (dst i k)) →ₐ[R]
    PrincipalFanRestrictionTarget (principalOccurrenceFan x i) k l)

local notation "c" => principalOccurrenceAmbientRelations A B x.source t


variable [Finite ι] [Finite κ] [∀ i, Finite (J i)]

/-- The complete mixed-source conclusion for the actual geometric diagram. -/
def PrincipalOccurrenceDiagramResult (ht : t ≤ x.target)
    (bs : ∀ i, Finset (relationIdeal R (A i)))
    (bt : ∀ j, Finset (relationIdeal R (B j))) : Prop :=
  FinitePolynomialCoefficients.OccurrenceMixedSourceRefinementResult (R := R)
    (O := PrincipalOccurrenceOpen (J := J)) (J := PrincipalOccurrenceDoubleLabel dst)
    (E := PrincipalOccurrenceCoordinateEdge dst) (H := PrincipalOccurrenceRestrictionEdge dst)
      (fun i ↦ numGenerators R (C i)) r I s
      (principalOccurrenceAmbientRelations A B bs bt)
      (principalOccurrenceDiagramDenominator e x)
      (principalOccurrenceCoordinateSource dst) (principalOccurrenceRestrictionSource dst)
      (fun i _ _ _ ↦ s i) (fun i _ _ _ _ ↦ c i)
      (fun _ _ _ _ ↦ le_rfl) (fun i _ _ _ _ ↦
        principalOccurrenceAmbientRelations_mono A B le_rfl ht i)
      (principalOccurrenceDiagramCoordinate (fun i k ↦ (e i k).toAlgHom))
      (principalOccurrenceDiagramRestriction e x)
      (principalOccurrenceDiagramFiniteCoordinate (fun i k ↦ (e i k).toAlgHom) x)
      (principalOccurrenceDiagramFiniteRestriction e x t ρ)

/-- Apply simultaneous refinement before extracting the geometric stage. -/
theorem exists_principalOccurrence_diagram_result
    (ht : t ≤ x.target)
    (hρ : ∀ i k l,
      (principalFanRestrictionProjection (e i) (principalOccurrenceFan x i) k l).comp (ρ i k l) =
      (principalFanOriginalRestriction (e i) (principalOccurrenceFan x i) k l).comp
        (principalStageMap R (B (dst i k)) (b (dst i k)) (t (dst i k))))
    (bs : ∀ i, Finset (relationIdeal R (A i)))
    (bt : ∀ j, Finset (relationIdeal R (B j))) :
    PrincipalOccurrenceDiagramResult e x t ρ ht bs bt := by
  exact FinitePolynomialCoefficients.exists_occurrence_mixed_source_refinement_result
    (R := R)
    (O := PrincipalOccurrenceOpen (J := J)) (J := PrincipalOccurrenceDoubleLabel dst)
    (E := PrincipalOccurrenceCoordinateEdge dst) (H := PrincipalOccurrenceRestrictionEdge dst)
      (fun i ↦ numGenerators R (C i)) r I s
      (principalOccurrenceAmbientRelations A B bs bt)
      (principalOccurrenceDiagramDenominator e x)
      (principalOccurrenceCoordinateSource dst) (principalOccurrenceRestrictionSource dst)
      (fun i _ _ _ ↦ s i) (fun i _ _ _ _ ↦ c i)
      (fun _ _ _ _ ↦ le_rfl) (fun i _ _ _ _ ↦
        principalOccurrenceAmbientRelations_mono A B le_rfl ht i)
      (principalOccurrenceDiagramCoordinate (fun i k ↦ (e i k).toAlgHom))
      (principalOccurrenceDiagramRestriction e x)
      (principalOccurrenceDiagramFiniteCoordinate (fun i k ↦ (e i k).toAlgHom) x)
      (principalOccurrenceDiagramFiniteRestriction e x t ρ)
      (principalOccurrenceDiagramCoordinate_recovery (fun i k ↦ (e i k).toAlgHom) x)
      (principalOccurrenceDiagramFiniteRestriction_recovery e x t ρ hρ)

end FLT.Mazur.FiniteTypeRelationModel
