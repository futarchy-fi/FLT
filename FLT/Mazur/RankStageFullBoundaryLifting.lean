/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFullBoundaryRestriction
public import FLT.Mazur.RankStageStructureMaps
public import FLT.Mazur.AffineFiniteEtaleFullBoundaryCoefficients

/-!
# Prescribed full boundary lifts on affine rank stages

Finite etale trace lifting applies to the whole stage when it is affine.
It simultaneously preserves a lower full coefficient and a prescribed higher
boundary value. No named core is required to be closed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance fullLiftOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance fullLiftOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance fullLiftOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
local notation "I" k:max => rankStageBoundaryIdeal (p := p) n k J
local notation "B" k:max => rankStageFullBoundaryInvariants e n J hJ k
attribute [local irreducible] rankStageFirst rankStageSecond rankStageInvariantTransition

include hf in
/-- Every full boundary invariant lifts on an affine full rank stage. -/
theorem exists_rankStage_full_initial_boundary_lift (k : ℕ)
    [IsAffine (rankThickening (Over.mk p) n k)] (y : B k) :
    ∃ z : rankStageInvariants e n k, (I k).subschemeι.appTop z.val = y.val := by
  let _ := rankStageFirst_finite (p := p) n k
  let _ := rankStageStructure_separated (p := p) n f k
  exact AffineFiniteEtaleFullBoundaryCoefficients.exists_initial_lift
    _ _ (rankThickeningMap (Over.mk p) n k ≫ f)
    (rankStageStructure_equalizes e n f hf k) (rankStageEquivalence e n k)
    (I k) (rankStageBoundaryIdeal_invariant e n k J hJ) y

include hf in
/-- An affine full stage lifts both the lower invariant and the higher boundary coefficient. -/
theorem exists_rankStage_full_prescribed_boundary_lift {k l : ℕ} (h : k ≤ l)
    [IsAffine (rankThickening (Over.mk p) n l)]
    (x : rankStageInvariants e n k) (y : B l)
    (hxy : (I k).subschemeι.appTop x.val =
      (rankStageFullBoundaryTransition (p := p) n J h).appTop y.val) :
    ∃ z : rankStageInvariants e n l, rankStageInvariantTransition e n h z = x ∧
      (I l).subschemeι.appTop z.val = y.val := by
  let _ : IsAffine (rankThickening (Over.mk p) n k) :=
    isAffine_of_isAffineHom (rankStageTransition (Over.mk p) n h)
  let _ := rankStageFirst_finite (p := p) n l
  let _ := rankStageStructure_separated (p := p) n f l
  exact AffineFiniteEtaleFullBoundaryCoefficients.exists_prescribed_lift
    _ _ (rankThickeningMap (Over.mk p) n l ≫ f)
    (rankStageStructure_equalizes e n f hf l) (rankStageEquivalence e n l)
    (I l) (rankStageBoundaryIdeal_invariant e n l J hJ) _ _
    (rankStageTransition (Over.mk p) n h) (rankStageRelationTransition (p := p) n h)
    (rankStageRelationTransition_isPullback n h) (rankStageRelationTransition_second e n h)
    (I k) (rankStageBoundaryIdeal_transition n h J)
    (rankStageInvariantTransition e n h)
    (rankStageInvariantTransition_val e n h) x y hxy

include hf hJ in
/-- Full homogeneous corrections lift through every affine rank-stage transition. -/
theorem exists_rankStage_full_boundary_zero_lift {k l : ℕ} (h : k ≤ l)
    [IsAffine (rankThickening (Over.mk p) n l)] (x : rankStageInvariants e n k)
    (hx : (I k).subschemeι.appTop x.val = 0) :
    ∃ z : rankStageInvariants e n l, rankStageInvariantTransition e n h z = x ∧
      (I l).subschemeι.appTop z.val = 0 := by
  apply exists_rankStage_full_prescribed_boundary_lift e n J hJ f hf h x 0
  simpa only [ZeroMemClass.coe_zero, map_zero] using hx

end FLT.Mazur.EquivalenceRelationOrderedFrames
