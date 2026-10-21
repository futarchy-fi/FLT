/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageGlobalBoundaryCoreCorrection
public import FLT.Mazur.RankStageOriginalCompatibleScalars

/-!
# Compatible core algebras over unchanged original invariant scalars

Refinement acts on entire compatible towers and commutes with the original
scalar action. The homogeneous ideal retains the full boundary at all orders.
These constructions do not require affine full stages or clopen cores.
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
local instance cochainAlgOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance cochainAlgOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance cochainAlgOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition

/-- Original full-source invariant scalars act on the actual compatible core tower. -/
@[instance_reducible]
def rankStageOriginalCoreAlgebra :
    Algebra (compatibleFunctions p q) (rankStageCompatibleCoreInvariants e n a ha) :=
  ((rankStageCompatibleCoreRestriction e n a ha).comp
    (rankStageOriginalCompatibleScalars e n)).toAlgebra

attribute [local instance] rankStageOriginalCoreAlgebra

/-- The entire homogeneous compatible core ideal, including every full boundary order. -/
def rankStageCompatibleCoreBoundaryKernel (J : A.IdealSheafData) :
    Ideal (rankStageCompatibleCoreInvariants e n a ha) where
  carrier := {v | ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop
    (v.val k).val = 0}
  zero_mem' := fun k ↦ map_zero _
  add_mem' := by
    intro v w hv hw k
    change (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop
      ((v.val k).val + (w.val k).val) = 0
    rw [map_add, hv k, hw k, add_zero]
  smul_mem' s v hv := fun k ↦ by
    change (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop
      ((s.val k).val * (v.val k).val) = 0
    rw [map_mul, hv k, mul_zero]

/-- Membership is literal full boundary vanishing at every order. -/
theorem mem_rankStageCompatibleCoreBoundaryKernel (J : A.IdealSheafData)
    (v : rankStageCompatibleCoreInvariants e n a ha) :
    v ∈ rankStageCompatibleCoreBoundaryKernel e n a ha J ↔
      ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (v.val k).val = 0 :=
  Iff.rfl

variable (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)
  (h : ∀ k, rankStageCore e n b hb k ≤ rankStageCore e n a ha k)

/-- Refinement of whole compatible core towers is linear over unchanged original scalars. -/
def rankStageCompatibleCoreRefinement :
    rankStageCompatibleCoreInvariants e n a ha →ₐ[compatibleFunctions p q]
      rankStageCompatibleCoreInvariants e n b hb where
  __ := CompatibleRingTower.map _ _ (fun k ↦ rankStageCoreRefinement e n a b ha hb k (h k))
    (fun k l hkl v ↦ (rankStageCoreRefinement_transition e n a b ha hb hkl (h k) (h l) v).symm)
  commutes' s := by
    apply Subtype.ext
    funext k
    change rankStageCoreRefinement e n a b ha hb k (h k)
      (rankStageGlobalCoreRestriction e n a ha k (rankStageOriginalInvariantRestriction e n k s)) =
        rankStageGlobalCoreRestriction e n b hb k (rankStageOriginalInvariantRestriction e n k s)
    exact rankStageGlobalCoreRestriction_refine e n a ha b hb k (h k) _

/-- Every literal coefficient of refinement is the original full section restriction. -/
theorem rankStageCompatibleCoreRefinement_val (v : rankStageCompatibleCoreInvariants e n a ha)
    (k : ℕ) :
    (rankStageCompatibleCoreRefinement e n a ha b hb h v).val k =
      rankStageCoreRefinement e n a b ha hb k (h k) (v.val k) := rfl

end FLT.Mazur.EquivalenceRelationOrderedFrames
