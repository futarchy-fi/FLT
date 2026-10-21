/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousCochainScalarObstruction
public import FLT.Mazur.RankStageCoreCochainMaps

/-!
# The actual compatible rank-core correction cokernel

Every source coordinate is a homogeneous compatible tower on a whole core.
The map takes its actual coboundary on every overlap. Thus the distinguished
class tests simultaneous cochain splitting, including all order equations.
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
local instance correctionCokernelOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance correctionCokernelOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance correctionCokernelOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
local notation "C" j:max => rankStageCompatibleCoreInvariants e n (c j) (hc j)
local notation "O" i:max j:max => rankStageCompatibleCoreInvariants e n (c i * c j)
  (rankStageProduct_domain n (c i) (c j) (hc i))
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition
  rankStageCompatibleCoreRefinement
  HomogeneousCochainCorrection.cochains HomogeneousCochainCorrection.difference
  HomogeneousCochainCorrection.correctionImage HomogeneousCochainCorrection.obstruction
  HomogeneousCochainCorrection.scalarIdeal

variable (J : A.IdealSheafData)
local notation "L" => rankStageCochainLeft e n c hc
local notation "R" => rankStageCochainRight e n c hc
local notation "K" => fun j ↦ rankStageCompatibleCoreBoundaryKernel e n (c j) (hc j) J

/-- The image of actual full homogeneous compatible core cochains in all overlap towers. -/
noncomputable def rankStageCoreCorrectionImage :
    Submodule (compatibleFunctions p q) (∀ i j, O i j) :=
  HomogeneousCochainCorrection.correctionImage L R K

/-- The full overlap obstruction in the actual cochain correction cokernel. -/
noncomputable def rankStageCoreCorrectionClass (v : ∀ j, C j) :
    (∀ i j, O i j) ⧸ rankStageCoreCorrectionImage e n c hc J :=
  HomogeneousCochainCorrection.obstruction L R K v

/-- Scalars permitting full compatible homogeneous corrections, in the original invariant ring. -/
noncomputable def rankStageCoreCorrectionIdeal (v : ∀ j, C j) :
    Ideal (compatibleFunctions p q) :=
  HomogeneousCochainCorrection.scalarIdeal L R K v

end FLT.Mazur.EquivalenceRelationOrderedFrames
