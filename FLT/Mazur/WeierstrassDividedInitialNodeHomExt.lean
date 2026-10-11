/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialNodeBranches
public import FLT.Mazur.WeierstrassDividedInitialIndexedNodeCover

/-!
# Arbitrary-target uniqueness on the original initial chart

Agreement on the two complete conic parameters and incidence line determines
both full node charts, hence their original indexed atlas object.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => residue_tangent_isUnit D

variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) j hj ⟶ Y)
  (hL : initialGlobalIncidenceLine hπ data D j hj hstart hk ≫ f =
    initialGlobalIncidenceLine hπ data D j hj hstart hk ≫ g)

include hL in
/-- The complete first node is determined by its original conic and incidence restrictions. -/
theorem initialGlobalFirstNode_hom_ext
    (hP : initialGlobalConicFirstParameter hπ data D j hj hstart hk ≫ f =
      initialGlobalConicFirstParameter hπ data D j hj hstart hk ≫ g) :
    initialGlobalResidueFirstNode hπ data D j hj hstart hk ≫ f =
      initialGlobalResidueFirstNode hπ data D j hj hstart hk ≫ g := by
  apply (fullNodeBranches_isPushout a c ha).hom_ext
  · apply (cancel_epi (fullNodeConicParameterIso a c ha).hom).mp
    simpa only [Category.assoc, initialGlobalFirstNode_conicBranch_assoc] using hP
  · simpa only [initialGlobalFirstNode_incidenceBranch_assoc] using
      congrArg (fun q => NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫ q) hL

include hL in
/-- The opposite full node retains the original translated incidence restriction. -/
theorem initialGlobalSecondNode_hom_ext
    (hP : initialGlobalConicSecondParameter hπ data D j hj hstart hk ≫ f =
      initialGlobalConicSecondParameter hπ data D j hj hstart hk ≫ g) :
    initialGlobalResidueSecondNode hπ data D j hj hstart hk ≫ f =
      initialGlobalResidueSecondNode hπ data D j hj hstart hk ≫ g := by
  apply (fullNodeBranches_isPushout (-a) c (ha).neg).hom_ext
  · apply (cancel_epi (fullNodeConicParameterIso (-a) c (ha).neg).hom).mp
    simpa only [Category.assoc, initialGlobalSecondNode_conicBranch_assoc] using hP
  · rw [initialGlobalSecondNode_incidenceBranch_assoc,
      initialGlobalSecondNode_incidenceBranch_assoc, hL]

include hL in
/-- Both original node charts determine the complete last indexed atlas object. -/
theorem initialGlobalParameters_indexed_hom_ext
    (hP₁ : initialGlobalConicFirstParameter hπ data D j hj hstart hk ≫ f =
      initialGlobalConicFirstParameter hπ data D j hj hstart hk ≫ g)
    (hP₂ : initialGlobalConicSecondParameter hπ data D j hj hstart hk ≫ f =
      initialGlobalConicSecondParameter hπ data D j hj hstart hk ≫ g) :
    globalTensorAtlasMap hπ data K j hj (Fin.succ ⟨j + 1, by omega⟩) ≫ f =
      globalTensorAtlasMap hπ data K j hj (Fin.succ ⟨j + 1, by omega⟩) ≫ g := by
  apply (initialIndexedNodeOpenCover hπ data D j hj hstart hk).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · change initialIndexedNodeMap _ _ _ _ _ _ _ 0 ≫ _ =
      initialIndexedNodeMap _ _ _ _ _ _ _ 0 ≫ _
    simp only [← Category.assoc, initialIndexedNodeMap_first_global]
    exact initialGlobalFirstNode_hom_ext hπ data D j hj hstart hk f g hL hP₁
  · change initialIndexedNodeMap _ _ _ _ _ _ _ 1 ≫ _ =
      initialIndexedNodeMap _ _ _ _ _ _ _ 1 ≫ _
    simp only [← Category.assoc, initialIndexedNodeMap_second_global]
    exact initialGlobalSecondNode_hom_ext hπ data D j hj hstart hk f g hL hP₂

end FLT.Mazur.WeierstrassDividedDepth
