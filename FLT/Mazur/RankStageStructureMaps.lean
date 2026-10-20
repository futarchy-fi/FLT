/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreBoundaryCoefficients

/-!
# Original base maps of infinitesimal rank stages

Separate the geometric structure-map proofs from coefficient elaboration.
The original separated base map still equalizes both full stage endpoints.
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
local instance structureMapOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance structureMapOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance structureMapOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]

omit [QuasiCompact p] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] [IsAffine S] in
/-- Each rank thickening keeps the separated map to the original affine base. -/
theorem rankStageStructure_separated (k : ℕ) :
    IsSeparated (rankThickeningMap (Over.mk p) n k ≫ f) := by
  unfold rankThickeningMap
  infer_instance

omit [IsAffine A] [LocallyQuasiFinite p] [IsAffine S] [IsSeparated f] in
include hf in
/-- Both complete rank-stage endpoints have the same original base map. -/
theorem rankStageStructure_equalizes (k : ℕ) :
    rankStageFirst (p := p) n k ≫ (rankThickeningMap (Over.mk p) n k ≫ f) =
      rankStageSecond e n k ≫ (rankThickeningMap (Over.mk p) n k ≫ f) := by
  rw [← Category.assoc, ← (rankStageFirst_isPullback (p := p) n k).w,
    Category.assoc, hf, ← Category.assoc, ← rankStageSecond_map, Category.assoc]

end FLT.Mazur.EquivalenceRelationOrderedFrames
