/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitInitialCharts
public import FLT.Mazur.WeierstrassDividedPositiveSplitInitialIndexedDesc
public import FLT.Mazur.WeierstrassDividedPositiveSplitLocalDescRecovery
public import FLT.Mazur.WeierstrassDividedInitialNodeBranches
import all FLT.Mazur.WeierstrassDividedPositiveSplitInitialNodeDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitInitialIndexedDesc

/-!
# Initial descent recovers the original positive-start atlas map

Applying the constructed initial descent to the actual cyclic components
recovers both original full node inclusions and the entire initial chart map.
This checks the conic coordinates and normalized exterior simultaneously.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => residue_tangent_isUnit D
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 d) (Data.factor6 d))
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp

local notation "F" => fun i => Over.Hom.left (Z i)
local notation "w" => positiveSplitCycleComponent_scheme_endpoints hπ data D s hs hstart hk hp

/-- Initial descent on the actual cyclic family recovers the original first full node. -/
theorem positiveSplitInitialFirstNodeDesc_original :
    positiveSplitInitialFirstNodeDesc data D s hk F w =
      initialGlobalResidueFirstNode hπ data D (s + 1) hs hstart (by omega) := by
  apply (fullNodeBranches_isPushout a c ha).hom_ext
  · apply (cancel_epi ((conicZeroAffineIso c hc) ≪≫
      fullNodeConicParameterIso a c ha).hom).mp
    simp only [Iso.trans_hom, Category.assoc, positiveSplitInitialFirstNodeDesc_conic,
      initialGlobalFirstNode_conicBranch, positiveSplitCycleComponent_initial_first_chart]
  · rw [positiveSplitInitialFirstNodeDesc_exterior,
      initialGlobalFirstNode_incidenceBranch, positiveSplitCycleComponent_incidence_chart]

/-- Initial descent on the actual cyclic family recovers the original second full node. -/
theorem positiveSplitInitialSecondNodeDesc_original :
    positiveSplitInitialSecondNodeDesc data D s hk F w =
      initialGlobalResidueSecondNode hπ data D (s + 1) hs hstart (by omega) := by
  apply (fullNodeBranches_isPushout (-a) c (ha).neg).hom_ext
  · apply (cancel_epi ((conicZeroAffineIso c hc) ≪≫
      fullNodeConicParameterIso (-a) c (ha).neg).hom).mp
    simp only [Iso.trans_hom, Category.assoc, positiveSplitInitialSecondNodeDesc_conic,
      initialGlobalSecondNode_conicBranch, positiveSplitCycleComponent_initial_second_chart]
  · rw [positiveSplitInitialSecondNodeDesc_exterior,
      initialGlobalSecondNode_incidenceBranch, positiveSplitCycleComponent_incidence_chart]

/-- Initial descent recovers the whole actual original indexed chart inclusion. -/
theorem positiveSplitInitialIndexedDesc_original :
    positiveSplitInitialIndexedDesc hπ data D s hs hstart hk F w =
      globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 3, by omega⟩ := by
  apply (initialIndexedNodeOpenCover hπ data D (s + 1) hs hstart (by omega)).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · change initialIndexedNodeMap _ _ _ _ _ _ _ 0 ≫ _ =
      initialIndexedNodeMap _ _ _ _ _ _ _ 0 ≫ _
    erw [positiveSplitInitialIndexedDesc_first, initialIndexedNodeMap_first_global,
      positiveSplitInitialFirstNodeDesc_original]
  · change initialIndexedNodeMap _ _ _ _ _ _ _ 1 ≫ _ =
      initialIndexedNodeMap _ _ _ _ _ _ _ 1 ≫ _
    erw [positiveSplitInitialIndexedDesc_second, initialIndexedNodeMap_second_global,
      positiveSplitInitialSecondNodeDesc_original]

end FLT.Mazur.WeierstrassDividedDepth
