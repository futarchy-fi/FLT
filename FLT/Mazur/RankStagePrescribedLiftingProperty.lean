/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageStructureMaps
public import FLT.Mazur.FiniteEtaleNamedDomainBoundaryLifting

/-!
# Simultaneous prescribed boundary lifts between rank orders

An invariant on a lower named core extends to a higher invariant with any
prescribed full higher boundary value agreeing on the exact lower boundary.
The conclusion retains both independent endpoints and every boundary equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance prescribedPropertyOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance prescribedPropertyOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance prescribedPropertyOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
local notation "U" => rankStageCore e n a ha
local notation "hU" => rankStageCore_invariant e n a ha
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J
local notation "C" => rankStageCoreInvariants e n a ha
local notation "B" => rankStageCoreBoundaryInvariants e n a ha J hJ

attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageFirst rankStageSecond
  rankStageCoreBoundaryMap

include hf in
/-- The simultaneous full-boundary lifting property on each pair of fixed rank cores. -/
theorem rankStageCore_hasLifts {k l : ℕ} (h : k ≤ l) :
    FiniteRelationPrescribedLifting.HasLifts
      ((rankStageFirst (p := p) n l).resLE (U l) _ le_rfl)
      ((rankStageSecond e n l).resLE (U l) _ (hU l).le)
      ((rankStageFirst (p := p) n k).resLE (U k) _ le_rfl)
      ((rankStageSecond e n k).resLE (U k) _ (hU k).le)
      (rankStageCoreMap e n a ha h) (I l)
      (rankStageCoreBoundaryIdeal_invariant e n a ha J hJ l) (I k)
      (rankStageCoreBoundaryIdeal_transition e n a ha J h) := by
  let _ := rankStageFirst_finite (p := p) n l
  let _ := rankStageStructure_separated (p := p) n f l
  exact FiniteEtaleNamedDomainBoundaryLifting.hasLifts
    _ _ _ _ (rankStageTransition (Over.mk p) n h) (rankStageRelationTransition (p := p) n h)
    (rankStageRelationTransition_isPullback n h) (rankStageRelationTransition_second e n h)
    (U l) (U k) (hU l) (hU k) (rankStageCore_preimage e n a ha h).symm
    (rankThickeningMap (Over.mk p) n l ≫ f) (rankStageStructure_equalizes e n f hf l)
    (rankStageEquivalence e n l) (rankStageCore_affine e n a ha l)
    (rankStageCore_affine e n a ha k) (I l)
    (rankStageCoreBoundaryIdeal_invariant e n a ha J hJ l) (I k)
    (rankStageCoreBoundaryIdeal_transition e n a ha J h)

end FLT.Mazur.EquivalenceRelationOrderedFrames
