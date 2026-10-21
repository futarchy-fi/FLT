/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryRelationPullback

/-!
# Exact order transitions for original-scalar endpoint equations

The original scalar structure map commutes with every boundary order map.
For test endpoints related by that exact map, vanishing of the full endpoint
quotient equations is equivalent at the two orders. This retains the full
scheme test, not merely its reduced support or its underlying point pair.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance quotientTransOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance quotientTransOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance quotientTransOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
set_option quotPrecheck false
local notation "C" k:max => rankStageCore e n a ha k
local notation "r" k:max => (rankStageFirst (p := p) n k).resLE (C k) _ le_rfl
local notation "s" k:max => (rankStageSecond e n k).resLE (C k) _
  (rankStageCore_invariant e n a ha k).le
local notation "I" k:max => rankStageCoreBoundaryIdeal e n a ha J k
local notation "hI" k:max => rankStageCoreBoundaryIdeal_invariant e n a ha J hJ k
local notation "rI" k:max => pullback.snd (r k) (I k).subschemeι
local notation "sI" k:max => InvariantIdealRelation.snd (I k) (r k) (s k) (hI k)
local notation "f" k:max => rankStageBoundaryOriginalScalars e n a ha J k
local notation "he" k:max => rankStageBoundaryOriginalScalars_condition e n a ha J hJ k
local notation "c" k:max => pullback.lift (rI k) (sI k) (he k)
variable {k l : ℕ} (h : k ≤ l)
local notation "b" => rankStageCoreBoundaryMap e n a ha J h

/-- The exact closed order map is over the unchanged original invariant scalar ring. -/
@[reassoc]
theorem rankStageBoundaryOriginalScalars_transition : b ≫ f l = f k := by
  unfold rankStageBoundaryOriginalScalars
  rw [← Category.assoc, rankStageCoreOriginalBoundaryMap_transition]

attribute [local irreducible] rankStageBoundaryOriginalScalars
variable {T : Scheme.{0}}

/-- Original scalar compatibility of tests survives every actual boundary order map. -/
theorem rankStage_boundary_test_scalar_transition (x y : T ⟶ (I k).subscheme)
    (hxy : x ≫ f k = y ≫ f k) : (x ≫ b) ≫ f l = (y ≫ b) ≫ f l := by
  simpa only [Category.assoc, rankStageBoundaryOriginalScalars_transition] using hxy

local notation "hxy'" x:max y:max hxy:max =>
  rankStage_boundary_test_scalar_transition e n a ha J h x y hxy

/-- Full quotient equations are equivalent on exactly transitioned test endpoints. -/
theorem rankStage_boundary_endpoint_equations_transition (x y : T ⟶ (I k).subscheme)
    (hxy : x ≫ f k = y ≫ f k) :
    (RingHom.ker (c k).appTop.hom ≤ RingHom.ker (pullback.lift x y hxy).appTop.hom) ↔
      RingHom.ker (c l).appTop.hom ≤
        RingHom.ker (pullback.lift (x ≫ b) (y ≫ b) (hxy' x y hxy)).appTop.hom := by
  rw [rankStage_boundary_quotient_iff_original_arrow e n a ha J hJ k x y hxy,
    rankStage_boundary_quotient_iff_original_arrow e n a ha J hJ l (x ≫ b) (y ≫ b) (hxy' x y hxy)]
  simp only [Category.assoc, rankStageCoreOriginalBoundaryMap_transition]

end FLT.Mazur.EquivalenceRelationOrderedFrames
