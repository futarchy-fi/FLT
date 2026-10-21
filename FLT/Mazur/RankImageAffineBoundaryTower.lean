/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageAffineBoundaryCoreSelection

/-!
# Full boundary towers over affine rank-image opens

An affine rank-image open makes every full ideal-power rank thickening affine.
This constructs global boundary lifts even when the exact rank support is not
open in its ambient and the original principal cores are not closed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance affineImageOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance affineImageOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance affineImageOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ)

omit [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] in
/-- Affineness of the rank-image open controls every full ideal-power thickening. -/
theorem rankThickening_isAffine_of_rankImage_affine
    (h : IsAffineOpen (rankImageOpen (Over.mk p) n)) (k : ℕ) :
    IsAffine (rankThickening (Over.mk p) n k) := by
  let _ : IsAffine (rankImageOpen (Over.mk p) n).toScheme := h
  change IsAffine (rankStratumIdeal (Over.mk p) n ^ (k + 1)).subscheme
  let _ : IsClosedImmersion (rankStratumIdeal (Over.mk p) n ^ (k + 1)).subschemeι :=
    inferInstance
  exact isAffine_of_isAffineHom (rankStratumIdeal (Over.mk p) n ^ (k + 1)).subschemeι

variable (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))

omit [IsAffine A] in
include hf in
/-- Affine rank-image geometry gives a compatible global lift of all original boundary values. -/
theorem exists_rankImage_affine_full_boundary_tower
    (h : IsAffineOpen (rankImageOpen (Over.mk p) n)) :
    ∃ v : ∀ k, rankStageInvariants e n k,
      (∀ k l (hkl : k ≤ l), rankStageInvariantTransition e n hkl (v l) = v k) ∧
      ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (v k).val =
        (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t.val := by
  let _ (k : ℕ) := rankThickening_isAffine_of_rankImage_affine (p := p) n h k
  exact exists_rankStage_affine_full_original_boundary_tower e n J hJ f hf t

include hf in
/-- A principal original rank-image open suffices, without any stationary-power assumption. -/
theorem exists_rankImage_principal_full_boundary_tower (a : Γ(A, ⊤))
    (ha : rankImageOpen (Over.mk p) n = A.basicOpen a) :
    ∃ v : ∀ k, rankStageInvariants e n k,
      (∀ k l (hkl : k ≤ l), rankStageInvariantTransition e n hkl (v l) = v k) ∧
      ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (v k).val =
        (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t.val := by
  apply exists_rankImage_affine_full_boundary_tower e n J hJ f hf t
  rw [ha]
  exact (isAffineOpen_top A).basicOpen a

end FLT.Mazur.EquivalenceRelationOrderedFrames
