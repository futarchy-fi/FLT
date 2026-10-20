/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageStructureMaps
public import FLT.Mazur.FiniteEtaleNamedBoundaryCoefficients

/-!
# Initial invariant lifts on coherent rank cores

Full boundary invariants lift at each rank order without any compatibility
assumption on an earlier coefficient. This supplies the initial tower value.
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
local instance initialBoundaryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance initialBoundaryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance initialBoundaryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
local notation "U" => rankStageCore e n a ha
local notation "hU" => rankStageCore_invariant e n a ha
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J
local notation "C" => rankStageCoreInvariants e n a ha
local notation "B" => rankStageCoreBoundaryInvariants e n a ha J hJ

attribute [local irreducible] rankStageCore rankStageFirst rankStageSecond

include hf in
/-- An arbitrary full boundary invariant has an initial lift on its named affine core. -/
theorem exists_rankStage_initial_boundary_lift (k : ℕ) (y : B k) :
    ∃ z : C k, (I k).subschemeι.appTop z.val = y.val := by
  let _ := rankStageFirst_finite (p := p) n k
  let _ := rankStageStructure_separated (p := p) n f k
  exact FiniteEtaleNamedBoundaryCoefficients.exists_lift _ _ (U k) (hU k)
    (rankThickeningMap (Over.mk p) n k ≫ f) (rankStageStructure_equalizes e n f hf k)
    (rankStageEquivalence e n k) (rankStageCore_affine e n a ha k) (I k)
    (rankStageCoreBoundaryIdeal_invariant e n a ha J hJ k) y

end FLT.Mazur.EquivalenceRelationOrderedFrames
