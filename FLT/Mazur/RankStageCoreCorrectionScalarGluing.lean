/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreCorrectionGluing

/-!
# Exact original scalar criterion for full boundary gluing

The scalar ideal is precisely the set of original scalars for which the
scaled original boundary admits one global compatible tower. The criterion
retains all orders and all full boundary values on the finite core cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance scalarGlueOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarGlueOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarGlueOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hc : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hcore : ∀ (c : C) k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen c.val.2 ≤
    rankStageCore e n c.val.1 (hc c) k)
  (hcover : exactRank (Over.mk p) n ⊆ ⋃ c ∈ C, (A.basicOpen c.2 : Set A))
  (J : A.IdealSheafData)
local notation "a" => fun c : C ↦ Prod.fst (Subtype.val c)
local notation "U" c:max k:max => rankStageCore e n (Prod.fst (Subtype.val c)) (hc c) k
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition rankStageCoreCorrectionObstruction

include hcore hcover in
/-- Exact scalar membership is equivalent to global solvability of the scaled full boundary. -/
theorem mem_rankStageCoreCorrectionIdeal_iff_scaled_global
    (v : ∀ c : C, rankStageCompatibleCoreInvariants e n c.val.1 (hc c))
    (t : Γ(J.subscheme, ⊤))
    (hv : ∀ c k, (rankStageCoreBoundaryIdeal e n c.val.1 (hc c) J k).subschemeι.appTop
      ((v c).val k).val = (rankStageCoreOriginalBoundaryMap e n c.val.1 (hc c) J k).appTop t)
    (s : compatibleFunctions p q) :
    s ∈ rankStageCoreCorrectionIdeal e n a hc J v ↔
      ∃ w : rankStageCompatibleInvariants e n,
        ∀ k, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop (w.val k).val =
          (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop
            (J.subschemeι.appTop s.val * t) := by
  rw [mem_rankStageCoreCorrectionIdeal_iff_scaled_class]
  apply rankStageCoreCorrectionObstruction_eq_zero_iff_global e n C hc hcore hcover J (s • v)
    (J.subschemeι.appTop s.val * t)
  intro c k
  simpa only [Pi.smul_apply, sub_zero] using
    rankStageCoreCorrection_scaled_boundary e n a hc J c s
      (v c) 0 t (hv c) (fun _ ↦ map_zero _) k

end FLT.Mazur.EquivalenceRelationOrderedFrames
