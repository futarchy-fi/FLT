/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreOverlapBoundary
public import FLT.Mazur.RankStageCoreRefinementCoefficients

/-!
# Constructed invariant homogeneous errors between different cores

The error lies in the actual full invariant ring of the affine intersection.
It corrects the two restricted lifts exactly, vanishes on the full original
boundary, and commutes with every order transition. Extending these overlap
corrections back to all ambient cores remains a separate gluing problem.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance overlapErrorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance overlapErrorOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance overlapErrorOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a b : Γ(A, ⊤))
  (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)
local notation "hab" => rankStageProduct_domain n a b ha
local notation "C" => rankStageCore e n (a * b) hab
local notation "L" k => rankStageCore_product_le_left e n a b ha hb k
local notation "R" k => rankStageCore_product_le_right e n a b ha hb k
local notation "α" k => rankStageCoreRefinement e n a (a * b) ha hab k (L k)
local notation "β" k => rankStageCoreRefinement e n b (a * b) hb hab k (R k)
attribute [local irreducible] rankStageCore

/-- The full invariant overlap error is constructed from the two actual coefficients. -/
def rankStageInvariantOverlapError (k : ℕ)
    (v : rankStageCoreInvariants e n a ha k) (w : rankStageCoreInvariants e n b hb k) :
    rankStageCoreInvariants e n (a * b) hab k := (α k) v - (β k) w

/-- Subtracting the constructed error gives exact equality on the whole affine overlap. -/
theorem rankStageInvariantOverlapError_corrects (k : ℕ)
    (v : rankStageCoreInvariants e n a ha k) (w : rankStageCoreInvariants e n b hb k) :
    (α k) v - rankStageInvariantOverlapError e n a b ha hb k v w = (β k) w :=
  sub_sub_cancel _ _

/-- The exact overlap correction is compatible with all closed order transitions. -/
theorem rankStageInvariantOverlapError_transition {k l : ℕ} (hkl : k ≤ l)
    (v : rankStageCoreInvariants e n a ha l) (w : rankStageCoreInvariants e n b hb l) :
    rankStageCoreRestriction e n (a * b) hab hkl
        (rankStageInvariantOverlapError e n a b ha hb l v w) =
      rankStageInvariantOverlapError e n a b ha hb k
        (rankStageCoreRestriction e n a ha hkl v)
        (rankStageCoreRestriction e n b hb hkl w) := by
  unfold rankStageInvariantOverlapError
  rw [map_sub]
  exact congrArg₂ (fun x y ↦ x - y)
    (rankStageCoreRefinement_transition e n a (a * b) ha hab hkl (L k) (L l) v)
    (rankStageCoreRefinement_transition e n b (a * b) hb hab hkl (R k) (R l) w)

/-- The constructed invariant error vanishes on the full original boundary of the overlap. -/
theorem rankStageInvariantOverlapError_boundary_zero (J : A.IdealSheafData) (k : ℕ)
    (v : rankStageCoreInvariants e n a ha k) (w : rankStageCoreInvariants e n b hb k)
    (t : Γ(J.subscheme, ⊤))
    (hv : (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop v.val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t)
    (hw : (rankStageCoreBoundaryIdeal e n b hb J k).subschemeι.appTop w.val =
      (rankStageCoreOriginalBoundaryMap e n b hb J k).appTop t) :
    (rankStageCoreBoundaryIdeal e n (a * b) hab J k).subschemeι.appTop
      (rankStageInvariantOverlapError e n a b ha hb k v w).val = 0 := by
  let _ : IsAffine (C k).toScheme := rankStageCore_affine e n (a * b) hab k
  have he := rankStage_distinct_core_boundary_difference e n k a b ha hb J
    ((rankThickening (Over.mk p) n k).homOfLE (L k))
    ((rankThickening (Over.mk p) n k).homOfLE (R k))
    (by rw [rankStageCoreRefinement_original, rankStageCoreRefinement_original]) v w t hv hw
  rw [rankStageCoreRefinement_original, rankStageCoreOriginalMap_ideal] at he
  rw [← (rankStageCoreBoundaryIdeal e n (a * b) hab J k).ker_subschemeι_app
    ⟨⊤, isAffineOpen_top _⟩] at he
  exact he

end FLT.Mazur.EquivalenceRelationOrderedFrames
