/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalBoundaryRestriction
public import FLT.Mazur.RankStagePrescribedBoundaryTower
public import FLT.Mazur.RankStageInitialBoundaryLifting

/-!
# Compatible full invariant towers lifting prescribed original boundary data

The full original boundary section determines every higher boundary value.
Simultaneous lifting constructs compatible full invariants with exactly those
values. The result does not descend the tower to the unchanged original source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance originalTowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance originalTowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance originalTowerOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
local notation "C" => rankStageCoreInvariants e n a ha
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J
local notation "ρ" => rankStageCoreRestriction e n a ha

attribute [local irreducible] rankStageCore rankStageCoreRestriction rankStageCoreMap
  rankStageFirst rankStageSecond rankThickening
  rankStageCoreBoundaryIdeal rankStageCoreBoundaryMap rankStageOriginalBoundaryRestriction

include hf in
/-- One original boundary section prescribes every value of an actual compatible invariant tower. -/
theorem exists_rankStage_original_boundary_tower
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ v : ∀ k : ℕ, C k,
      (∀ k, (I k).subschemeι.appTop (v k).val =
        (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t.val) ∧
      ∀ k l (h : k ≤ l), ρ h (v l) = v k := by
  let u (k : ℕ) := rankStageOriginalBoundaryRestriction e n a ha J hJ k t
  obtain ⟨z, hz⟩ := exists_rankStage_initial_boundary_lift e n a ha J hJ f hf 0 (u 0)
  obtain ⟨v, _, hb, hc⟩ := exists_rankStage_prescribed_boundary_tower e n a ha J hJ f hf u
    (fun k ↦ rankStageOriginalBoundaryRestriction_compatible e n a ha J hJ (Nat.le_succ k) t)
    z hz
  refine ⟨v, ?_, hc⟩
  intro k
  exact (hb k).trans (rankStageOriginalBoundaryRestriction_val e n a ha J hJ k t)

end FLT.Mazur.EquivalenceRelationOrderedFrames
