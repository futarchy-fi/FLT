/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedOlderResidueNodes

/-!
# Ordered older nodes in the actual global atlas

The constructed finite older nodes embed into the projective residue model.
Their exact global indices, union and complete original cubic contractions
are retained by the existing tensor atlas comparisons.
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
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "N" => MiddleNodeOpen (residue R (Data.b6 e))
local notation "g" => finiteLocalTensorEmbedding hπ data K (j + 1 + r) hr
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The retained first ordered node in every available later global residue model. -/
def olderGlobalResidueFirstNode :
    Spec (.of N) ⟶ finiteGlobalTensorModel hπ data K (j + 1 + r) hr :=
  olderResidueFirstNode hπ data D j hj r hr hk0 hk ≫ g

instance olderGlobalResidueFirstNode_isOpenImmersion :
    IsOpenImmersion (olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The older first node retains its exact inclusion at global index r+2. -/
@[reassoc] theorem olderGlobalResidueFirstNode_eq_index :
    residueMiddleFirstNodeChart D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) ≫
      (olderSuccessiveTensorAtlasIso hπ data K j hj r hr).hom ≫
        globalTensorAtlasMap hπ data K (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) =
      olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalTensorChart_eq_index]
  simp only [olderGlobalResidueFirstNode, olderResidueFirstNode,
    olderGlobalTensorChart, Category.assoc]

/-- The first older node keeps every original cubic function after global embedding. -/
@[reassoc] theorem olderGlobalResidueFirstNode_toCurve :
    olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      Spec.map (CommRingCat.ofHom
        (finiteFirstNodeContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [olderGlobalResidueFirstNode, Category.assoc, finiteLocalTensorEmbedding_toCurve,
    olderResidueFirstNode_toCurve]

/-- The ordered first older node keeps its residue-field structure. -/
@[reassoc] theorem olderGlobalResidueFirstNode_structure :
    olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  rw [olderGlobalResidueFirstNode, Category.assoc, finiteLocalTensorEmbedding_structure,
    olderResidueFirstNode_structure]

/-- The retained second ordered node in every available later global residue model. -/
def olderGlobalResidueSecondNode :
    Spec (.of N) ⟶ finiteGlobalTensorModel hπ data K (j + 1 + r) hr :=
  olderResidueSecondNode hπ data D j hj r hr hk0 hk ≫ g

instance olderGlobalResidueSecondNode_isOpenImmersion :
    IsOpenImmersion (olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The older second node retains its exact inclusion at global index r+2. -/
@[reassoc] theorem olderGlobalResidueSecondNode_eq_index :
    residueMiddleSecondNodeChart D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) ≫
      (olderSuccessiveTensorAtlasIso hπ data K j hj r hr).hom ≫
        globalTensorAtlasMap hπ data K (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) =
      olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalTensorChart_eq_index]
  simp only [olderGlobalResidueSecondNode, olderResidueSecondNode,
    olderGlobalTensorChart, Category.assoc]

/-- The second older node keeps every original cubic function after global embedding. -/
@[reassoc] theorem olderGlobalResidueSecondNode_toCurve :
    olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      Spec.map (CommRingCat.ofHom
        (finiteSecondNodeContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [olderGlobalResidueSecondNode, Category.assoc, finiteLocalTensorEmbedding_toCurve,
    olderResidueSecondNode_toCurve]

/-- The ordered second older node keeps its residue-field structure. -/
@[reassoc] theorem olderGlobalResidueSecondNode_structure :
    olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K N)) := by
  rw [olderGlobalResidueSecondNode, Category.assoc, finiteLocalTensorEmbedding_structure,
    olderResidueSecondNode_structure]

/-- Both ordered neighborhoods cover exactly the full older global tensor chart. -/
theorem olderGlobalResidueNodes_range :
    Set.range (olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk) ∪
      Set.range (olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk) =
        Set.range (olderGlobalTensorChart hπ data K j hj r hr) := by
  have h := olderResidueNodes_range hπ data D j hj r hr hk0 hk
  rw [← olderSuccessiveTensorChart_range] at h
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · have hp := Set.mem_union_left
        (Set.range (olderResidueSecondNode hπ data D j hj r hr hk0 hk))
        (Set.mem_range_self (f := olderResidueFirstNode hπ data D j hj r hr hk0 hk) p)
      rw [h] at hp
      obtain ⟨t, ht⟩ := hp
      exact ⟨t, congrArg g ht⟩
    · have hp := Set.mem_union_right
        (Set.range (olderResidueFirstNode hπ data D j hj r hr hk0 hk))
        (Set.mem_range_self (f := olderResidueSecondNode hπ data D j hj r hr hk0 hk) p)
      rw [h] at hp
      obtain ⟨t, ht⟩ := hp
      exact ⟨t, congrArg g ht⟩
  · rintro ⟨p, rfl⟩
    have hp := Set.mem_range_self (f := olderSuccessiveTensorChart hπ data j hj r hr K) p
    rw [← h] at hp
    rcases hp with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Or.inl ⟨t, congrArg g ht⟩
    · exact Or.inr ⟨t, congrArg g ht⟩

end FLT.Mazur.WeierstrassDividedDepth
