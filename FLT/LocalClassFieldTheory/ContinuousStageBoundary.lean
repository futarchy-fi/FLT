/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCochainColimit
public import FLT.LocalClassFieldTheory.FilteredComplexDescent

/-!
# Boundary detection after finite-stage refinement

A cochain at any independently chosen stage becomes a continuous boundary
exactly when it becomes a boundary at a later finite stage. The refinement
and its bounding cochain are constructed from continuous finite descent.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- Boundaries in the continuous complex are detected at a common refinement
of the supplied finite stage and a constructed stage for the bounding cochain. -/
theorem continuousStage_boundary_iff (N : (OpenNormalSubgroup G)ᵒᵈ) (n m : ℕ)
    (z : ((invariantStageDiagram k G M).obj N).X m) :
    (∃ b : (continuousCochains k G M).X n,
      ((continuousCochains k G M).d n m).hom b =
        ((continuousStageInflation k G M N).f m).hom z) ↔
    ∃ (P : (OpenNormalSubgroup G)ᵒᵈ) (f : N ⟶ P)
      (b : ((invariantStageDiagram k G M).obj P).X n),
      (((invariantStageDiagram k G M).obj P).d n m).hom b =
        (((invariantStageDiagram k G M).map f).f m).hom z := by
  constructor
  · rintro ⟨b, hb⟩
    exact complexCocone_boundary (invariantStageDiagram k G M) (continuousStageCocone k G M)
      (continuousStageInflation_injective k G M)
      (continuousStageInflation_jointly_surjective k G M) N n m z b hb
  · rintro ⟨P, f, b, hb⟩
    refine ⟨((continuousStageInflation k G M P).f n).hom b, ?_⟩
    calc
      _ = ((continuousStageInflation k G M P).f m).hom
          ((((invariantStageDiagram k G M).obj P).d n m).hom b) :=
        congrArg (fun g => g.hom b) ((continuousStageInflation k G M P).comm n m)
      _ = _ := by
        rw [hb]
        exact complexCocone_naturality (invariantStageDiagram k G M)
          (continuousStageCocone k G M) f m z

end LocalClassFieldTheory
