/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalBoundaryCoefficients
public import FLT.Mazur.InvariantIdealRelationCoefficientMembership

/-!
# Original full boundary data on every coherent rank-stage core

A single original boundary invariant pulls back to full boundary invariants
on the named cores. The exact closed maps make these values compatible at
all pairs of orders, before any choices of ambient invariant lifts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance originalInvariantOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance originalInvariantOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance originalInvariantOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local notation "U" => rankStageCore e n a ha
local notation "hU" => rankStageCore_invariant e n a ha
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J

attribute [local irreducible] rankStageCore rankStageFirst rankStageSecond

/-- Pullback of a prescribed original full boundary invariant to each named core. -/
def rankStageOriginalBoundaryRestriction (k : ℕ) :
    compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ) →
      rankStageCoreBoundaryInvariants e n a ha J hJ k :=
  fun t ↦ ⟨(rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t.val,
    @InvariantIdealRelationCoefficients.pullback_mem D A
    (rankStageFirst (p := p) n k ⁻¹ᵁ U k).toScheme (U k).toScheme p q
    ((rankStageFirst (p := p) n k).resLE (U k) _ le_rfl)
    ((rankStageSecond e n k).resLE (U k) _ (hU k).le)
    (rankStageCoreOriginalMap e n a ha k) (rankStageCoreOriginalArrow e n a ha k)
    (rankStageCoreOriginalArrow_first e n a ha k) (rankStageCoreOriginalArrow_second e n a ha k)
    J hJ (I k) (rankStageCoreBoundaryIdeal_invariant e n a ha J hJ k)
    (rankStageCoreOriginalMap_ideal e n a ha J k) t⟩

/-- Prescribed values are literal restrictions of the original full boundary coefficient. -/
theorem rankStageOriginalBoundaryRestriction_val (k : ℕ)
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    (rankStageOriginalBoundaryRestriction e n a ha J hJ k t).val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t.val := rfl

/-- All prescribed original boundary values are compatible on the exact closed transitions. -/
theorem rankStageOriginalBoundaryRestriction_compatible {k l : ℕ} (h : k ≤ l)
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    (rankStageCoreBoundaryMap e n a ha J h).appTop
        (rankStageOriginalBoundaryRestriction e n a ha J hJ l t).val =
      (rankStageOriginalBoundaryRestriction e n a ha J hJ k t).val := by
  rw [rankStageOriginalBoundaryRestriction_val, rankStageOriginalBoundaryRestriction_val]
  exact rankStageOriginalBoundaryCoefficients_compatible e n a ha J h t.val

end FLT.Mazur.EquivalenceRelationOrderedFrames
