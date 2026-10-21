/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFullBoundaryGluing
public import FLT.Mazur.RankStageInvariantTransitions
public import FLT.Mazur.InvariantIdealRelationCoefficientMembership

/-!
# Full original boundary coefficients on the entire rank tower

The original invariant boundary section restricts to the full rank schemes,
without choosing any core. Every order map retains the entire pulled ideal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance fullOriginalOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance fullOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance fullOriginalOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local notation "I" k:max => rankStageBoundaryIdeal (p := p) n k J

/-- Full invariant boundary coefficients on the entire rank thickening. -/
abbrev rankStageFullBoundaryInvariants (k : ℕ) :=
  compatibleFunctions (pullback.snd (rankStageFirst (p := p) n k) (I k).subschemeι)
    (rankStageBoundarySecond e n k J hJ)

/-- The boundary order map is constructed from equality of the unchanged full ideals. -/
def rankStageFullBoundaryTransition {k l : ℕ} (h : k ≤ l) :
    (I k).subscheme ⟶ (I l).subscheme :=
  IdealSheafClosedTransitions.map (I k) (I l) (rankStageTransition (Over.mk p) n h)
    (rankStageBoundaryIdeal_transition n h J)

omit [QuasiCompact p] [IsLocallyNoetherian A] [IsAffine A] [LocallyQuasiFinite p] in
/-- Boundary transitions commute with the original full boundary map. -/
@[reassoc]
theorem rankStageFullBoundaryTransition_original {k l : ℕ} (h : k ≤ l) :
    rankStageFullBoundaryTransition (p := p) n J h ≫
        rankStageFullOriginalBoundaryMap (p := p) n J l =
      rankStageFullOriginalBoundaryMap (p := p) n J k := by
  unfold rankStageFullBoundaryTransition rankStageFullOriginalBoundaryMap
  rw [IdealSheafClosedTransitions.map_comp]
  congr 1
  exact rankStageTransition_map (Over.mk p) n h

attribute [local irreducible] rankStageFirst rankStageSecond

/-- Original full boundary invariants restrict to the entire rank stage. -/
def rankStageFullBoundaryRestriction (k : ℕ)
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) : rankStageFullBoundaryInvariants e n J hJ k :=
  ⟨(rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t.val,
    InvariantIdealRelationCoefficients.pullback_mem p q _ _
      (rankThickeningMap (Over.mk p) n k) (rankStageArrow (p := p) n k)
      (rankStageFirst_isPullback (p := p) n k).w (rankStageSecond_map e n k).symm
      J hJ (I k) (rankStageBoundaryIdeal_invariant e n k J hJ) rfl t⟩

attribute [local irreducible] rankStageFullOriginalBoundaryMap rankStageFullBoundaryTransition

omit [IsAffine A] [LocallyQuasiFinite p] in
/-- The original full boundary values satisfy all order-transition equations. -/
theorem rankStageFullBoundaryRestriction_compatible {k l : ℕ} (h : k ≤ l)
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    (rankStageFullBoundaryTransition (p := p) n J h).appTop
        (rankStageFullBoundaryRestriction e n J hJ l t).val =
      (rankStageFullBoundaryRestriction e n J hJ k t).val := by
  change (rankStageFullBoundaryTransition (p := p) n J h ≫
    rankStageFullOriginalBoundaryMap (p := p) n J l).appTop t.val = _
  rw [rankStageFullBoundaryTransition_original]
  rfl

end FLT.Mazur.EquivalenceRelationOrderedFrames
