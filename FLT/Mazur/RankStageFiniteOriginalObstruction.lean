/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteScalarObstruction
public import FLT.Mazur.RankStageOriginalCompatibleScalars

/-!
# One original-scalar obstruction for finitely many all-order rank errors

All selected ranks use the unchanged original invariant ring. The joint
scalar quotient is finite over that ring. A common radical witness gives
one exponent for all selected ranks and all orders, with genuine compatible
homogeneous numerators. Existence of such a radical witness is not assumed
by the construction and must be proved separately from geometry.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance finiteObstructionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteObstructionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteObstructionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable {ι : Type*} (n : ι → ℕ) (a : ι → Γ(A, ⊤))
  (ha : ∀ j, A.basicOpen (a j) ≤ rankImageOpen (Over.mk p) (n j))
  (J : A.IdealSheafData)
  (x : ∀ j, rankStageCompatibleCoreInvariants e (n j) (a j) (ha j))

/-- One original-scalar ideal for the complete selected error family, at every order. -/
def rankStageFamilyNumeratorIdeal : Ideal (compatibleFunctions p q) :=
  FiniteScalarObstruction.jointIdeal
    (fun j ↦ rankStageOriginalNumeratorIdeal e (n j) (a j) (ha j) J (x j))

/-- The whole error vector has a finite cyclic obstruction over original scalars. -/
theorem rankStageFamilyNumeratorQuotient_finite :
    Module.Finite (compatibleFunctions p q)
      ((compatibleFunctions p q) ⧸ rankStageFamilyNumeratorIdeal e n a ha J x) := inferInstance

/-- One admissible scalar gives a simultaneously chosen full homogeneous numerator family. -/
theorem mem_rankStageFamilyNumeratorIdeal (s : compatibleFunctions p q) :
    s ∈ rankStageFamilyNumeratorIdeal e n a ha J x ↔
      ∃ w : ∀ j k, rankStageInvariants e (n j) k,
        (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e (n j) J k) ∧
        (∀ j k l (h : k ≤ l), rankStageInvariantTransition e (n j) h (w j l) = w j k) ∧
        ∀ j k, rankStageGlobalCoreRestriction e (n j) (a j) (ha j) k (w j k) =
          rankStageGlobalCoreRestriction e (n j) (a j) (ha j) k
            (rankStageOriginalInvariantRestriction e (n j) k s) * (x j).val k := by
  constructor
  · intro hs
    have hh (j : ι) := (mem_rankStageOriginalNumeratorIdeal e (n j) (a j) (ha j) J
      (x j) s).mp ((FiniteScalarObstruction.mem_jointIdeal _ s).mp hs j)
    choose w hw ht he using hh
    exact ⟨w, hw, ht, he⟩
  · rintro ⟨w, hw, ht, he⟩
    exact (FiniteScalarObstruction.mem_jointIdeal _ s).mpr (fun j ↦
      (mem_rankStageOriginalNumeratorIdeal e (n j) (a j) (ha j) J (x j) s).mpr
        ⟨w j, hw j, ht j, he j⟩)

variable [Finite ι]

/-- Separate all-order radical witnesses give one exponent across the entire finite rank family. -/
theorem exists_rankStage_family_uniform_numerators (s : compatibleFunctions p q)
    (hs : ∀ j, s ∈ (rankStageOriginalNumeratorIdeal e (n j) (a j) (ha j) J (x j)).radical) :
    ∃ (N : ℕ) (w : ∀ j k, rankStageInvariants e (n j) k),
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e (n j) J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e (n j) h (w j l) = w j k) ∧
      ∀ j k, rankStageGlobalCoreRestriction e (n j) (a j) (ha j) k (w j k) =
        (rankStageGlobalCoreRestriction e (n j) (a j) (ha j) k
          (rankStageOriginalInvariantRestriction e (n j) k s)) ^ N * (x j).val k := by
  obtain ⟨N, hN⟩ := FiniteScalarObstruction.exists_uniform_power
    (fun j ↦ rankStageOriginalNumeratorIdeal e (n j) (a j) (ha j) J (x j)) s hs
  obtain ⟨w, hw, ht, he⟩ := (mem_rankStageFamilyNumeratorIdeal e n a ha J x (s ^ N)).mp
    ((FiniteScalarObstruction.mem_jointIdeal _ (s ^ N)).mpr hN)
  refine ⟨N, w, hw, ht, fun j k ↦ ?_⟩
  simpa only [map_pow] using he j k

end FLT.Mazur.EquivalenceRelationOrderedFrames
