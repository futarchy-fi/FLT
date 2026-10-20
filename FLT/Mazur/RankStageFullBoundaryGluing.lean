/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenCoverFullBoundaryDetection
public import FLT.Mazur.RankStageCompatibleCoreTowerGluing

/-!
# Prescribed full original boundary values survive rank-stage gluing

The stage boundary is the entire pullback of the original ideal. Its map to
the original boundary is Cartesian. Gluing compatible core lifts preserves
this boundary value at every order as well as every order transition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections IdealSheafClosedTransitions
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance fullGlueOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance fullGlueOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance fullGlueOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCore
variable (n : ℕ) (J : A.IdealSheafData)

/-- The full stage boundary maps to the unchanged original boundary. -/
def rankStageFullOriginalBoundaryMap (k : ℕ) :
    (rankStageBoundaryIdeal (p := p) n k J).subscheme ⟶ J.subscheme :=
  map _ J (rankThickeningMap (Over.mk p) n k) rfl

variable (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (ha : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hcore : ∀ (c : C) k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen c.val.2 ≤
    rankStageCore e n c.val.1 (ha c) k)
  (hcover : exactRank (Over.mk p) n ⊆ ⋃ c ∈ C, (A.basicOpen c.2 : Set A))

include hcore hcover in
/-- Full original boundary equality can be checked on the selected affine cores. -/
theorem rankStage_full_boundary_of_core_values (k : ℕ)
    (s : Γ(rankThickening (Over.mk p) n k, ⊤)) (t : Γ(J.subscheme, ⊤))
    (h : ∀ c : C, (rankStageCoreBoundaryIdeal e n c.val.1 (ha c) J k).subschemeι.appTop
        ((rankStageCore e n c.val.1 (ha c) k).ι.appTop s) =
      (rankStageCoreOriginalBoundaryMap e n c.val.1 (ha c) J k).appTop t) :
    (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop s =
      (rankStageFullOriginalBoundaryMap n J k).appTop t := by
  apply OpenCoverFullBoundaryDetection.boundary_eq_of_local
    (fun c : C ↦ rankStageCore e n c.val.1 (ha c) k)
    (rankStage_finite_core_cover e n C ha hcore hcover k)
  intro c
  have hh := h c
  dsimp only [rankStageCoreBoundaryIdeal] at hh
  rw [hh]
  change (rankStageCoreOriginalBoundaryMap e n c.val.1 (ha c) J k).appTop t =
    (map _ _ (rankStageCore e n c.val.1 (ha c) k).ι rfl ≫
      rankStageFullOriginalBoundaryMap n J k).appTop t
  apply congrArg (fun f : (rankStageCoreBoundaryIdeal e n c.val.1 (ha c) J k).subscheme ⟶
    J.subscheme ↦ f.appTop t)
  apply (cancel_mono J.subschemeι).mp
  simp only [rankStageCoreOriginalBoundaryMap, rankStageFullOriginalBoundaryMap,
    map_inclusion, Category.assoc, map_inclusion_assoc, rankStageCoreOriginalMap,
    rankStageCoreBoundaryIdeal]

include hcore hcover in
/-- Compatible full core lifts construct a full boundary lift at every rank order. -/
theorem exists_rankStage_full_boundary_tower_of_errors_zero
    (t : Γ(J.subscheme, ⊤))
    (v : ∀ (c : C) k, rankStageCoreInvariants e n c.val.1 (ha c) k)
    (hv : ∀ (c d : C) k,
      rankStageInvariantOverlapError e n c.val.1 d.val.1 (ha c) (ha d) k (v c k) (v d k) = 0)
    (ht : ∀ (c : C) k l (hkl : k ≤ l),
      rankStageCoreRestriction e n c.val.1 (ha c) hkl (v c l) = v c k)
    (hb : ∀ (c : C) k,
      (rankStageCoreBoundaryIdeal e n c.val.1 (ha c) J k).subschemeι.appTop (v c k).val =
        (rankStageCoreOriginalBoundaryMap e n c.val.1 (ha c) J k).appTop t) :
    ∃ s : ∀ k, compatibleFunctions (rankStageFirst (p := p) n k) (rankStageSecond e n k),
      (∀ (c : C) k, (rankStageCore e n c.val.1 (ha c) k).ι.appTop (s k).val =
        (v c k).val) ∧
      (∀ k l (hkl : k ≤ l),
        (rankStageTransition (Over.mk p) n hkl).appTop (s l).val = (s k).val) ∧
      ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (s k).val =
        (rankStageFullOriginalBoundaryMap n J k).appTop t := by
  obtain ⟨s, hs, hc⟩ := exists_rankStage_invariant_tower_of_errors_zero
    e n C ha hcore hcover v hv ht
  refine ⟨s, hs, hc, fun k ↦ ?_⟩
  apply rankStage_full_boundary_of_core_values e n J C ha hcore hcover k
  intro c
  rw [hs c k]
  exact hb c k

end FLT.Mazur.EquivalenceRelationOrderedFrames
