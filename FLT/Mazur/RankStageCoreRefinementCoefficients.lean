/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenCoefficientRestriction
public import FLT.Mazur.RankStageCoreIntersections
public import FLT.Mazur.RankStageOriginalBoundaryCoefficients

/-!
# Full coefficient restriction between distinct original cores

An inclusion of cores induces a map of their entire invariant rings. The
maps commute with every order transition and retain the original source map.
The product core supplies concrete inclusions for every pair of parameters.
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
local instance refinementOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance refinementOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance refinementOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a b : Γ(A, ⊤))
  (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)
local notation "C" => rankStageCore e n a ha
local notation "C'" => rankStageCore e n b hb
attribute [local irreducible] rankStageCore

/-- Refinement of original cores restricts the full invariant coefficient ring. -/
def rankStageCoreRefinement (k : ℕ) (h : C' k ≤ C k) :
    rankStageCoreInvariants e n a ha k →+* rankStageCoreInvariants e n b hb k :=
  InvariantOpenCoefficientRestriction.restriction _ _ (C k) (C' k)
    (rankStageCore_invariant e n a ha k) (rankStageCore_invariant e n b hb k) h

/-- The refinement coefficient is the literal source restriction. -/
theorem rankStageCoreRefinement_val (k : ℕ) (h : C' k ≤ C k)
    (v : rankStageCoreInvariants e n a ha k) :
    (rankStageCoreRefinement e n a b ha hb k h v).val =
      ((rankThickening (Over.mk p) n k).homOfLE h).appTop v.val := rfl

/-- The overlap restriction retains the unchanged original source map. -/
@[reassoc]
theorem rankStageCoreRefinement_original (k : ℕ) (h : C' k ≤ C k) :
    (rankThickening (Over.mk p) n k).homOfLE h ≫
      rankStageCoreOriginalMap e n a ha k = rankStageCoreOriginalMap e n b hb k := by
  simp only [rankStageCoreOriginalMap, Scheme.homOfLE_ι_assoc]

/-- Cross-core refinement commutes with every closed order transition. -/
theorem rankStageCoreRefinement_transition {k l : ℕ} (hkl : k ≤ l)
    (hk : C' k ≤ C k) (hl : C' l ≤ C l) (v : rankStageCoreInvariants e n a ha l) :
    rankStageCoreRestriction e n b hb hkl (rankStageCoreRefinement e n a b ha hb l hl v) =
      rankStageCoreRefinement e n a b ha hb k hk (rankStageCoreRestriction e n a ha hkl v) := by
  apply Subtype.ext
  simp only [rankStageCoreRestriction_val, rankStageCoreRefinement_val]
  change (rankStageCoreMap e n b hb hkl ≫
    (rankThickening (Over.mk p) n l).homOfLE hl).appTop v.val =
      ((rankThickening (Over.mk p) n k).homOfLE hk ≫
        rankStageCoreMap e n a ha hkl).appTop v.val
  apply congrArg (fun f : (C' k).toScheme ⟶ (C l).toScheme ↦ f.appTop v.val)
  apply (cancel_mono (C l).ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, rankStageCoreMap_inclusion,
    Scheme.homOfLE_ι_assoc]

include hb in
/-- The product core restricts to the first chosen original core. -/
theorem rankStageCore_product_le_left (k : ℕ) :
    rankStageCore e n (a * b) (rankStageProduct_domain n a b ha) k ≤ C k := by
  rw [rankStageCore_mul e n a b ha hb]
  exact inf_le_left

/-- The same product core restricts to the second, independently chosen core. -/
theorem rankStageCore_product_le_right (k : ℕ) :
    rankStageCore e n (a * b) (rankStageProduct_domain n a b ha) k ≤ C' k := by
  rw [rankStageCore_mul e n a b ha hb]
  exact inf_le_right

end FLT.Mazur.EquivalenceRelationOrderedFrames
