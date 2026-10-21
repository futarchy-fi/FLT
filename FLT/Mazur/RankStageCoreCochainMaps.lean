/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCompatibleCoreAlgebra

/-!
# Whole compatible rank-core cochain restriction maps

Whole compatible core towers restrict to each ordered overlap as algebras
over the unchanged original invariant ring.
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
local instance correctionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance correctionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance correctionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
local notation "C" j:max => rankStageCompatibleCoreInvariants e n (c j) (hc j)
local notation "O" i:max j:max => rankStageCompatibleCoreInvariants e n (c i * c j)
  (rankStageProduct_domain n (c i) (c j) (hc i))
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition
  rankStageCompatibleCoreRefinement
/-- Restriction from the first whole compatible core to its overlap. -/
def rankStageCochainLeft (i j : ι) : C i →ₐ[compatibleFunctions p q] O i j :=
  rankStageCompatibleCoreRefinement e n (c i) (hc i) (c i * c j)
    (rankStageProduct_domain n (c i) (c j) (hc i))
    (fun k ↦ rankStageCore_product_le_left e n (c i) (c j) (hc i) (hc j) k)

/-- Restriction from the second whole compatible core to the same overlap. -/
def rankStageCochainRight (i j : ι) : C j →ₐ[compatibleFunctions p q] O i j :=
  rankStageCompatibleCoreRefinement e n (c j) (hc j) (c i * c j)
    (rankStageProduct_domain n (c i) (c j) (hc i))
    (fun k ↦ rankStageCore_product_le_right e n (c i) (c j) (hc i) (hc j) k)

end FLT.Mazur.EquivalenceRelationOrderedFrames
