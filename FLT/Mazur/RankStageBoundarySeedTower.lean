/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreBoundaryTransitions

/-!
# Initial full boundary data lifts to a compatible rank-stage tower

An arbitrary invariant section on the full initial boundary has a lift to
compatible invariant coefficients at every rank order. The induced higher
boundary values are compatible; prescribing those values in advance still
requires surjectivity on the boundary kernels of the order transitions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance seedOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance seedOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance seedOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
local notation "U" => rankStageCore e n a ha
local notation "hU" => rankStageCore_invariant e n a ha
local notation "C" => rankStageCoreInvariants e n a ha

include hf in
/-- Every full initial boundary invariant admits an actual compatible invariant tower. -/
theorem exists_rankStage_boundary_seed_tower :
    let β := FiniteEtaleInvariantOpenBoundary.restriction
      (rankStageFirst (p := p) n 0) (rankStageSecond e n 0) (U 0) (hU 0)
      (rankStageBoundaryIdeal (p := p) n 0 J) (rankStageBoundaryIdeal_invariant e n 0 J hJ)
    ∀ t, ∃ v : ∀ k : ℕ, C k, β (v 0) = t ∧
      ∀ k l (h : k ≤ l), rankStageCoreRestriction e n a ha h (v l) = v k := by
  dsimp only
  intro t
  obtain ⟨z, hz⟩ := rankStage_boundaryRestriction_surjective e f hf J hJ n 0
    (U 0) (hU 0) (rankStageCore_affine e n a ha 0) t
  obtain ⟨v, hv, hc⟩ := exists_compatible_rankStageCore_coefficients e n a ha f hf z
  refine ⟨v, ?_, hc⟩
  rw [hv]
  exact hz

end FLT.Mazur.EquivalenceRelationOrderedFrames
