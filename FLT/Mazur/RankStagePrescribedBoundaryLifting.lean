/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStagePrescribedLiftingProperty
public import FLT.Mazur.FiniteRelationPrescribedLiftCoefficients

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
local instance prescribedOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance prescribedOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance prescribedOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
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

include hf hJ in
/-- The actual rank order transition lifts prescribed full higher boundary values. -/
theorem exists_rankStage_prescribed_boundary_lift {k l : ℕ} (h : k ≤ l)
    (x : C k) (y : B l)
    (hxy : (I k).subschemeι.appTop x.val =
      (rankStageCoreBoundaryMap e n a ha J h).appTop y.val) :
    ∃ z : C l, rankStageCoreRestriction e n a ha h z = x ∧
      (I l).subschemeι.appTop z.val = y.val := by
  exact FiniteRelationPrescribedLifting.exists_lift _ _ _ _
    (rankStageCoreMap e n a ha h) (I l)
    (rankStageCoreBoundaryIdeal_invariant e n a ha J hJ l) (I k)
    (rankStageCoreBoundaryIdeal_transition e n a ha J h)
    (rankStageCore_hasLifts e n a ha J hJ f hf h)
    (rankStageCoreRestriction e n a ha h) (rankStageCoreRestriction_val e n a ha h)
    x y hxy

include hf hJ in
/-- Exact boundary-zero invariant corrections extend through every rank order map. -/
theorem exists_rankStage_boundary_kernel_lift {k l : ℕ} (h : k ≤ l) (x : C k)
    (hx : (I k).subschemeι.appTop x.val = 0) :
    ∃ z : C l, rankStageCoreRestriction e n a ha h z = x ∧
      (I l).subschemeι.appTop z.val = 0 := by
  apply exists_rankStage_prescribed_boundary_lift e n a ha J hJ f hf h x 0
  simpa only [ZeroMemClass.coe_zero, map_zero] using hx

end FLT.Mazur.EquivalenceRelationOrderedFrames
