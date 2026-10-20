/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageInvariantOverlapErrors

/-!
# The full invariant correction cocycle on triple product cores

The differences already constructed on pairwise overlaps obey the cocycle
identity after restriction to the actual triple intersection. No extension
of an overlap correction to a larger domain is assumed here.
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
local instance cocycleOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance cocycleOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance cocycleOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a b c : Γ(A, ⊤))
  (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)
  (hc : A.basicOpen c ≤ rankImageOpen (Over.mk p) n)
attribute [local irreducible] rankStageCore

/-- Refinement through two intermediate cores is the direct full coefficient map. -/
theorem rankStageCoreRefinement_comp (k : ℕ)
    (hab : rankStageCore e n b hb k ≤ rankStageCore e n a ha k)
    (hbc : rankStageCore e n c hc k ≤ rankStageCore e n b hb k)
    (v : rankStageCoreInvariants e n a ha k) :
    rankStageCoreRefinement e n b c hb hc k hbc
        (rankStageCoreRefinement e n a b ha hb k hab v) =
      rankStageCoreRefinement e n a c ha hc k (hbc.trans hab) v :=
  InvariantOpenCoefficientRestriction.restriction_comp _ _ _ _ _ _ _ _ _ _ _

local notation "hab" => rankStageProduct_domain n a b ha
local notation "hbc" => rankStageProduct_domain n b c hb
local notation "hac" => rankStageProduct_domain n a c ha
local notation "ht" => rankStageProduct_domain n (a * b) c hab
local notation "T" k => rankStageCore e n (a * b * c) ht k

/-- The named triple product is exactly the intersection of all three full cores. -/
theorem rankStageCore_triple (k : ℕ) :
    (T k) = rankStageCore e n a ha k ⊓ rankStageCore e n b hb k ⊓
      rankStageCore e n c hc k := by
  rw [rankStageCore_mul e n (a * b) c hab hc, rankStageCore_mul e n a b ha hb]

include hc in
/-- The triple domain lies in the overlap of the second and third cores. -/
theorem rankStageCore_triple_le_bc (k : ℕ) :
    (T k) ≤ rankStageCore e n (b * c) hbc k := by
  rw [rankStageCore_triple e n a b c ha hb hc, rankStageCore_mul e n b c hb hc]
  exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

include hb hc in
/-- The triple domain also lies in the overlap of the first and third cores. -/
theorem rankStageCore_triple_le_ac (k : ℕ) :
    (T k) ≤ rankStageCore e n (a * c) hac k := by
  rw [rankStageCore_triple e n a b c ha hb hc, rankStageCore_mul e n a c ha hc]
  exact le_inf (inf_le_left.trans inf_le_left) inf_le_right

local notation "tab" k => rankStageCore_product_le_left e n (a * b) c hab hc k
local notation "tbc" k => rankStageCore_triple_le_bc e n a b c ha hb hc k
local notation "tac" k => rankStageCore_triple_le_ac e n a b c ha hb hc k

/-- The actual homogeneous differences satisfy the full triple-overlap cocycle. -/
theorem rankStageInvariantOverlapError_cocycle (k : ℕ)
    (u : rankStageCoreInvariants e n a ha k) (v : rankStageCoreInvariants e n b hb k)
    (w : rankStageCoreInvariants e n c hc k) :
    rankStageCoreRefinement e n (a * b) (a * b * c) hab ht k (tab k)
        (rankStageInvariantOverlapError e n a b ha hb k u v) +
      rankStageCoreRefinement e n (b * c) (a * b * c) hbc ht k (tbc k)
        (rankStageInvariantOverlapError e n b c hb hc k v w) =
      rankStageCoreRefinement e n (a * c) (a * b * c) hac ht k (tac k)
        (rankStageInvariantOverlapError e n a c ha hc k u w) := by
  simp only [rankStageInvariantOverlapError, map_sub, rankStageCoreRefinement_comp]
  exact sub_add_sub_cancel _ _ _

end FLT.Mazur.EquivalenceRelationOrderedFrames
