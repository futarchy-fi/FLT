/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreBoundaryCoefficients
public import FLT.Mazur.InvariantIdealRelationCoefficients

/-!
# Original full boundary data on every coherent rank-stage core

A single original boundary section pulls back to full boundary sections
on the named cores. The exact closed maps make these values compatible at
all pairs of orders, before any choices of ambient invariant lifts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance originalBoundaryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance originalBoundaryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance originalBoundaryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local notation "U" => rankStageCore e n a ha
local notation "hU" => rankStageCore_invariant e n a ha
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J

/-- The unchanged original source map of a named affine core. -/
def rankStageCoreOriginalMap (k : ℕ) : (U k).toScheme ⟶ A :=
  (U k).ι ≫ rankThickeningMap (Over.mk p) n k

/-- The entire named core relation maps to the original relation. -/
def rankStageCoreOriginalArrow (k : ℕ) :
    (rankStageFirst (p := p) n k ⁻¹ᵁ U k).toScheme ⟶ D :=
  (rankStageFirst (p := p) n k ⁻¹ᵁ U k).ι ≫ rankStageArrow (p := p) n k

/-- The first endpoint retains the actual original source. -/
theorem rankStageCoreOriginalArrow_first (k : ℕ) :
    rankStageCoreOriginalArrow e n a ha k ≫ p =
      (rankStageFirst (p := p) n k).resLE (U k) _ le_rfl ≫
        rankStageCoreOriginalMap e n a ha k := by
  rw [rankStageCoreOriginalArrow, rankStageCoreOriginalMap, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι, Category.assoc,
    (rankStageFirst_isPullback (p := p) n k).w, Category.assoc]

/-- The independent second endpoint retains the same original source map. -/
theorem rankStageCoreOriginalArrow_second (k : ℕ) :
    rankStageCoreOriginalArrow e n a ha k ≫ q =
      (rankStageSecond e n k).resLE (U k) _ (hU k).le ≫
        rankStageCoreOriginalMap e n a ha k := by
  rw [rankStageCoreOriginalArrow, rankStageCoreOriginalMap, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, rankStageSecond_map]

/-- The complete original boundary ideal pulls back to the named core boundary. -/
theorem rankStageCoreOriginalMap_ideal (k : ℕ) :
    J.comap (rankStageCoreOriginalMap e n a ha k) = I k := by
  rw [rankStageCoreOriginalMap, Scheme.IdealSheafData.comap_comp]
  rfl

/-- The actual map from the named full boundary to the unchanged original boundary. -/
def rankStageCoreOriginalBoundaryMap (k : ℕ) : (I k).subscheme ⟶ J.subscheme :=
  IdealSheafClosedTransitions.map (I k) J (rankStageCoreOriginalMap e n a ha k)
    (rankStageCoreOriginalMap_ideal e n a ha J k)

/-- Every order transition commutes with the map to the unchanged original boundary. -/
@[reassoc]
theorem rankStageCoreOriginalBoundaryMap_transition {k l : ℕ} (h : k ≤ l) :
    rankStageCoreBoundaryMap e n a ha J h ≫ rankStageCoreOriginalBoundaryMap e n a ha J l =
      rankStageCoreOriginalBoundaryMap e n a ha J k := by
  apply (cancel_mono J.subschemeι).mp
  simp only [rankStageCoreOriginalBoundaryMap, rankStageCoreBoundaryMap, Category.assoc,
    IdealSheafClosedTransitions.map_inclusion, IdealSheafClosedTransitions.map_inclusion_assoc,
    rankStageCoreOriginalMap]
  rw [rankStageCoreMap_inclusion_assoc, rankStageTransition_map]

/-- Full original boundary coefficients restrict compatibly at every pair of orders. -/
theorem rankStageOriginalBoundaryCoefficients_compatible {k l : ℕ} (h : k ≤ l)
    (t : Γ(J.subscheme, ⊤)) :
    (rankStageCoreBoundaryMap e n a ha J h).appTop
        ((rankStageCoreOriginalBoundaryMap e n a ha J l).appTop t) =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t := by
  change (rankStageCoreBoundaryMap e n a ha J h ≫
    rankStageCoreOriginalBoundaryMap e n a ha J l).appTop t = _
  rw [rankStageCoreOriginalBoundaryMap_transition]

end FLT.Mazur.EquivalenceRelationOrderedFrames
