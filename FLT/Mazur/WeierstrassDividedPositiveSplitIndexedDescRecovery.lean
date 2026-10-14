/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitLocalDescRecovery
public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedIndexedDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedIndexedDesc

/-!
# Positive-start descent recovers all original retained indexed inclusions

The original two-node covers identify the descended maps with every complete
retained atlas inclusion, with all source and target index transports explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
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
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "F" => fun i => Over.Hom.left (Z i)
local notation "w" => positiveSplitCycleComponent_scheme_endpoints hπ data D s hs hstart hk hp

section Earlier
variable (j : Fin (s + 1))
local notation "T" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s - j.val + 1) (by omega)))
  (Fin.mk (s - j.val + 2) (by omega)) (by rfl))
local notation "U" => olderIndexedNodeOpenCover hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)
local notation "M" => globalTensorAtlasMap hπ data K (s + 1) hs
  (Fin.mk (s - j.val + 2) (by omega))
local notation "Q" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega))

/-- The first retained atlas restriction has its exact original global target transport. -/
@[reassoc] theorem positiveSplitRetainedIndexed_first_global :
    (U).f (0 : Fin 2) ≫ T ≫ M =
      olderGlobalResidueFirstNode hπ data D j.val (by omega)
        (s - j.val) (by omega) (by omega) (by omega) ≫ Q := by
  rw [globalTensorAtlasMap_index_transport hπ data
    (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
    (Fin.succ ⟨s - j.val + 1, by omega⟩) ⟨s - j.val + 2, by omega⟩ (by rfl)]
  exact olderIndexedNodeMap_first_global_assoc hπ data D j.val (by omega)
    (s - j.val) (by omega) (by omega) (by omega) Q

/-- The second retained atlas restriction has its exact original global target transport. -/
@[reassoc] theorem positiveSplitRetainedIndexed_second_global :
    (U).f (1 : Fin 2) ≫ T ≫ M =
      olderGlobalResidueSecondNode hπ data D j.val (by omega)
        (s - j.val) (by omega) (by omega) (by omega) ≫ Q := by
  rw [globalTensorAtlasMap_index_transport hπ data
    (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
    (Fin.succ ⟨s - j.val + 1, by omega⟩) ⟨s - j.val + 2, by omega⟩ (by rfl)]
  exact olderIndexedNodeMap_second_global_assoc hπ data D j.val (by omega)
    (s - j.val) (by omega) (by omega) (by omega) Q

/-- Descent on the actual family recovers every complete retained atlas inclusion. -/
theorem positiveSplitCycleRetainedIndexedDesc_original :
    positiveSplitCycleRetainedIndexedDesc hπ data D s hs hstart hp j F w = M := by
  apply (cancel_epi T).mp
  apply (U).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · exact (positiveSplitCycleRetainedIndexedDesc_first
      hπ data D s hs hstart hp j F w).trans
      ((positiveSplitCycleFirstLocalDesc_original
        hπ data D s hs hstart hk hp j).trans
        (positiveSplitRetainedIndexed_first_global hπ data D s hs hstart hp j).symm)
  · exact (positiveSplitCycleRetainedIndexedDesc_second
      hπ data D s hs hstart hp j F w).trans
      ((positiveSplitCycleSecondLocalDesc_original
        hπ data D s hs hstart hk hp j).trans
        (positiveSplitRetainedIndexed_second_global hπ data D s hs hstart hp j).symm)

end Earlier

end FLT.Mazur.WeierstrassDividedDepth
