/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceDiagramFiniteRestrictions
public import FLT.Mazur.PrincipalOccurrenceStageFromDiagram
public import FLT.Mazur.PrincipalOccurrenceRefinedPaths
public import FLT.Mazur.PrincipalOccurrenceDiagramResult
public import FLT.Mazur.PrincipalOccurrenceRestrictionSquares

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
  FiniteRelationIterated.transition FiniteRelationLocalization.transition

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

/-- Refine actual coordinates and restrictions, retaining all old restriction squares. -/
theorem exists_principalOccurrence_diagram_refinement
    (ht : t ≤ x.target)
    (hρ : ∀ i k l,
      (principalFanRestrictionProjection (e i) (principalOccurrenceFan x i) k l).comp (ρ i k l) =
      (principalFanOriginalRestriction (e i) (principalOccurrenceFan x i) k l).comp
        (principalStageMap R (B (dst i k)) (b (dst i k)) (t (dst i k))))
    (bs : ∀ i, Finset (relationIdeal R (A i)))
    (bt : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ (y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)) (hxy : x ≤ y),
      bs ≤ y.source ∧ bt ≤ y.target ∧
      ∃ σ : ∀ i k l,
        PrincipalStage R (B (dst i k)) (b (dst i k)) (y.target (dst i k)) →ₐ[R]
          PrincipalFanOldRestrictionTarget (principalOccurrenceFan_mono hxy i) k l,
        PrincipalOccurrenceRestrictionOldSquares e x t ρ ht (y := y) hxy σ := by
  let f := fun i k ↦ (e i k).toAlgHom
  obtain ⟨q, hsq, hbq, F, G, hFOld, hGOld, hF, _hG⟩ :=
    exists_principalOccurrence_diagram_result e x t ρ ht hρ bs bt
  let F' := fun i k ↦ F (.inl i) (.inr (dst i k)) PUnit.unit
    (principalOccurrenceCoordinateEdge dst i k)
  let hF' := fun i k ↦ hF (.inl i) (.inr (dst i k)) PUnit.unit
    (principalOccurrenceCoordinateEdge dst i k)
  let y := principalOccurrenceStageOfDiagram f (fun i ↦ q (.inl i))
    (fun j ↦ q (.inr j)) F' hF'
  have hxy : x ≤ y := principalOccurrenceStageOfDiagram_le f
    (fun i ↦ q (.inl i)) (fun j ↦ q (.inr j)) F' hF' x
    (fun i ↦ hsq (.inl i)) (fun j ↦ hsq (.inr j))
    (fun i k ↦ hFOld (.inl i) (.inr (dst i k)) PUnit.unit
      (principalOccurrenceCoordinateEdge dst i k))
  refine ⟨y, hxy, fun i ↦ hbq (.inl i), fun j ↦ hbq (.inr j),
    fun i k l ↦ G (.inr (dst i k)) (.inr (dst i l)) PUnit.unit
      (principalOccurrenceDoubleLabel dst i k l) (principalOccurrenceRestrictionEdge dst i k l),
    fun i k l ↦ ?_⟩
  · exact hGOld (.inr (dst i k)) (.inr (dst i l)) PUnit.unit
      (principalOccurrenceDoubleLabel dst i k l) (principalOccurrenceRestrictionEdge dst i k l)

end FLT.Mazur.FiniteTypeRelationModel
