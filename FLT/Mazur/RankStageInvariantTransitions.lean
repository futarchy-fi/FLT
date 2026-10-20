/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageRelationTransitions
public import FLT.Mazur.AffineFiniteEtaleBoundarySurjectivity

/-!
# Invariant coefficient transitions for full rank stages

The contravariant ring maps preserve the complete original endpoint equalizers
and compose across orders. On affine stages they are surjective by the finite
etale relation trace theorem, with all trace charts constructed from geometry.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  (e : CategoryTheory.EquivalenceRelation p q) (n : ℕ)
local instance invariantTransitionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance invariantTransitionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance invariantTransitionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable {k l m : ℕ} (h : k ≤ l)

/-- Invariant coefficients on the entire relation at a specified infinitesimal order. -/
abbrev rankStageInvariants (k : ℕ) :=
  compatibleFunctions (rankStageFirst (p := p) n k) (rankStageSecond e n k)

/-- Actual coefficient restriction under the original ideal-power inclusion. -/
def rankStageInvariantTransition : rankStageInvariants e n l →+* rankStageInvariants e n k :=
  relationPullback _ _ _ _ (rankStageTransition (Over.mk p) n h)
    (rankStageRelationTransition (p := p) n h) (rankStageRelationTransition_first n h)
    (rankStageRelationTransition_second e n h)

/-- The invariant transition is literally restriction of the entire source coefficient. -/
theorem rankStageInvariantTransition_val (a : rankStageInvariants e n l) :
    (rankStageInvariantTransition e n h a).val =
      (rankStageTransition (Over.mk p) n h).appTop a.val := rfl

/-- Restricting in two steps gives the same full coefficient, with no reduction. -/
theorem rankStageInvariantTransition_comp (h' : l ≤ m) :
    (rankStageInvariantTransition e n h).comp (rankStageInvariantTransition e n h') =
      rankStageInvariantTransition e n (h.trans h') := by
  ext a
  change (rankStageTransition (Over.mk p) n h).appTop
    ((rankStageTransition (Over.mk p) n h').appTop a.val) = _
  change (rankStageTransition (Over.mk p) n h ≫
    rankStageTransition (Over.mk p) n h').appTop a.val = _
  rw [rankStageTransition_comp]
  rfl

instance rankStageTransition_closed :
    IsClosedImmersion (rankStageTransition (Over.mk p) n h) := by
  unfold rankStageTransition
  infer_instance

variable {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S)
  (hf : p ≫ f = q ≫ f) [IsSeparated f] [LocallyQuasiFinite p]

include hf in
/-- Every full lower-stage invariant lifts to an affine higher stage. -/
theorem rankStageInvariantTransition_surjective
    [IsAffine (rankThickening (Over.mk p) n l)] :
    Function.Surjective (rankStageInvariantTransition e n h) := by
  let _ : IsAffine (rankThickening (Over.mk p) n k) :=
    isAffine_of_isAffineHom (rankStageTransition (Over.mk p) n h)
  let _ := rankStageFirst_finite (p := p) n l
  let b := rankThickeningMap (Over.mk p) n l
  let _ : IsSeparated (b ≫ f) := by
    dsimp [b, rankThickeningMap]
    infer_instance
  have H : rankStageFirst (p := p) n l ≫ (b ≫ f) = rankStageSecond e n l ≫ (b ≫ f) := by
    rw [← Category.assoc, ← (rankStageFirst_isPullback (p := p) n l).w,
      Category.assoc, hf, ← Category.assoc, ← rankStageSecond_map, Category.assoc]
  exact AffineFiniteEtaleBoundarySurjectivity.boundary_invariant_surjective
    _ _ (b ≫ f) H (rankStageEquivalence e n l) _ _ _ _
    (rankStageRelationTransition_isPullback n h) (rankStageRelationTransition_second e n h)

end FLT.Mazur.EquivalenceRelationOrderedFrames
