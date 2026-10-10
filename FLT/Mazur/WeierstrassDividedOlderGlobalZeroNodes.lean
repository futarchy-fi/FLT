/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSuccessive
public import FLT.Mazur.WeierstrassSuccessiveXZeroNodeMaps

/-!
# The ordered full first nodes retained in every later global model

Both actual ambient node opens embed into the global model and cover the
whole original successive tensor chart, keeping the divided constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
open WeierstrassModificationX
local notation "ha" => D.a₁_unit.map (residue R)
local notation "g" => olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The first ordered full ambient node in the actual projective residue model. -/
def olderGlobalZeroFirstNode : Spec (.of (FullNodeOpen a c)) ⟶
    finiteGlobalTensorModel hπ data K (j + 1 + r) hr :=
  fullFirstNodeChart a c ha ≫ g

instance olderGlobalZeroFirstNode_isOpenImmersion :
    IsOpenImmersion (olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The first node retains its original residue-field structure in the global model. -/
@[reassoc] theorem olderGlobalZeroFirstNode_structure :
    olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K (FullNodeOpen a c))) := by
  rw [olderGlobalZeroFirstNode, Category.assoc, olderGlobalZeroSuccessiveChart_structure,
    fullFirstNodeChart_eq_spec, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fiberFullFirstNodeMap a c ha).commutes)

/-- The first global node keeps the full original cubic contraction. -/
@[reassoc] theorem olderGlobalZeroFirstNode_toCurve :
    olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      fullFirstNodeChart a c ha ≫ Spec.map (CommRingCat.ofHom
        (globalZeroSuccessiveContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [olderGlobalZeroFirstNode, Category.assoc, olderGlobalZeroSuccessiveChart_toCurve]

/-- The second ordered full ambient node in the actual projective residue model. -/
def olderGlobalZeroSecondNode : Spec (.of (FullNodeOpen (-a) c)) ⟶
    finiteGlobalTensorModel hπ data K (j + 1 + r) hr :=
  fullSecondNodeChart a c ha ≫ g

instance olderGlobalZeroSecondNode_isOpenImmersion :
    IsOpenImmersion (olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The second node retains its original residue-field structure in the global model. -/
@[reassoc] theorem olderGlobalZeroSecondNode_structure :
    olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K (FullNodeOpen (-a) c))) := by
  rw [olderGlobalZeroSecondNode, Category.assoc, olderGlobalZeroSuccessiveChart_structure,
    fullSecondNodeChart_eq_spec, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fiberFullSecondNodeMap a c ha).commutes)

/-- The second global node keeps the full original cubic contraction. -/
@[reassoc] theorem olderGlobalZeroSecondNode_toCurve :
    olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      fullSecondNodeChart a c ha ≫ Spec.map (CommRingCat.ofHom
        (globalZeroSuccessiveContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [olderGlobalZeroSecondNode, Category.assoc, olderGlobalZeroSuccessiveChart_toCurve]

/-- Both ordered full nodes cover every point of the original global successive chart. -/
theorem olderGlobalZeroNodes_range :
    Set.range (olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk) ∪
      Set.range (olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk) =
        Set.range (olderGlobalTensorChart hπ data K j hj r hr) := by
  rw [← olderGlobalZeroSuccessiveChart_range hπ data D j hj r hr hk0 hk]
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨fullFirstNodeChart a c ha p, rfl⟩
    · exact ⟨fullSecondNodeChart a c ha p, rfl⟩
  · rintro ⟨p, rfl⟩
    rcases fullNodeCharts_cover a c ha p with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
    · exact Or.inr ⟨t, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
