/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueLaurent
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedGlobalTensorAtlas
public import FLT.Mazur.WeierstrassDividedTensorAtlasComparison

/-!
# Terminal residue charts in the actual global atlas

The complete terminal tensor chart is a Laurent scheme at exact even middle
depth, and the oriented polygon node before middle depth. Both comparisons
retain the actual indexed inclusion, coefficient structure and cubic map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

section Laurent
variable (hp : 2 * (start + j) = depth)
local notation "e" => WeierstrassDilatation.residueLaurentIso D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The entire normalized terminal laurent chart in the projective residue model. -/
def terminalLaurentChart : Spec (.of (K[T;T⁻¹])) ⟶
    finiteGlobalTensorModel hπ data K j hj :=
  (e).hom ≫ globalDividedTensorChart hπ data K j hj

instance terminalLaurentChart_isOpenImmersion :
    IsOpenImmersion (terminalLaurentChart hπ data D j hj hk0 hk hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The normalized terminal chart is exactly the original indexed global chart one. -/
def terminalLaurentAtlasIso : Spec (.of (K[T;T⁻¹])) ≅
    globalTensorAtlasObject hπ data K j hj (Fin.succ 0) :=
  e ≪≫ finiteDividedTensorAtlasIso hπ data K j hj

/-- The comparison retains the actual map of the terminal indexed atlas. -/
@[reassoc] theorem terminalLaurentAtlasIso_map :
    (terminalLaurentAtlasIso hπ data D j hj hk0 hk hp).hom ≫
      globalTensorAtlasMap hπ data K j hj (Fin.succ 0) =
        terminalLaurentChart hπ data D j hj hk0 hk hp := by
  change ((e).hom ≫ (finiteDividedTensorAtlasIso hπ data K j hj).hom) ≫
    (finiteTensorAtlasMap hπ data K j hj 0 ≫ finiteLocalTensorEmbedding hπ data K j hj) = _
  rw [Category.assoc, finiteDividedTensorAtlasIso_map_assoc]
  rfl

/-- Normalization retains the complete original cubic contraction. -/
@[reassoc] theorem terminalLaurentChart_toCurve :
    terminalLaurentChart hπ data D j hj hk0 hk hp ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      (e).hom ≫ TensorOpenChart.projection ≫ toCurve d := by
  rw [terminalLaurentChart, Category.assoc, globalDividedTensorChart_toCurve]

/-- Normalization retains the residue-field structure on the whole terminal chart. -/
@[reassoc] theorem terminalLaurentChart_structure :
    terminalLaurentChart hπ data D j hj hk0 hk hp ≫ pullback.fst _ _ =
      (MultiplicativeGroupScheme.gm K).hom := by
  rw [terminalLaurentChart, Category.assoc, globalDividedTensorChart_structure]
  exact WeierstrassDilatation.residueLaurentIso_structure ..

/-- Normalization loses no points of the complete terminal divided tensor chart. -/
theorem terminalLaurentChart_range :
    Set.range (terminalLaurentChart hπ data D j hj hk0 hk hp) =
      Set.range (globalDividedTensorChart hπ data K j hj) := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(e).hom p, rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(e).inv p, ?_⟩
    have he : (e).hom ((e).inv p) = p :=
      congrArg (fun f => f p) (e).inv_hom_id
    change globalDividedTensorChart hπ data K j hj ((e).hom ((e).inv p)) = _
    rw [he]
end Laurent

section Node
variable (hp : 2 * (start + j) < depth)
local notation "e" => WeierstrassDilatation.residueNodeIso D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The entire normalized terminal node chart in the projective residue model. -/
def terminalNodeChart : PolygonNodeBranches.node K ⟶
    finiteGlobalTensorModel hπ data K j hj :=
  (e).hom ≫ globalDividedTensorChart hπ data K j hj

instance terminalNodeChart_isOpenImmersion :
    IsOpenImmersion (terminalNodeChart hπ data D j hj hk0 hk hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The normalized terminal chart is exactly the original indexed global chart one. -/
def terminalNodeAtlasIso : PolygonNodeBranches.node K ≅
    globalTensorAtlasObject hπ data K j hj (Fin.succ 0) :=
  e ≪≫ finiteDividedTensorAtlasIso hπ data K j hj

/-- The comparison retains the actual map of the terminal indexed atlas. -/
@[reassoc] theorem terminalNodeAtlasIso_map :
    (terminalNodeAtlasIso hπ data D j hj hk0 hk hp).hom ≫
      globalTensorAtlasMap hπ data K j hj (Fin.succ 0) =
        terminalNodeChart hπ data D j hj hk0 hk hp := by
  change ((e).hom ≫ (finiteDividedTensorAtlasIso hπ data K j hj).hom) ≫
    (finiteTensorAtlasMap hπ data K j hj 0 ≫ finiteLocalTensorEmbedding hπ data K j hj) = _
  rw [Category.assoc, finiteDividedTensorAtlasIso_map_assoc]
  rfl

/-- Normalization retains the complete original cubic contraction. -/
@[reassoc] theorem terminalNodeChart_toCurve :
    terminalNodeChart hπ data D j hj hk0 hk hp ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      (e).hom ≫ TensorOpenChart.projection ≫ toCurve d := by
  rw [terminalNodeChart, Category.assoc, globalDividedTensorChart_toCurve]

/-- Normalization retains the residue-field structure on the whole terminal chart. -/
@[reassoc] theorem terminalNodeChart_structure :
    terminalNodeChart hπ data D j hj hk0 hk hp ≫ pullback.fst _ _ =
      PolygonNodeBranches.toBase K := by
  rw [terminalNodeChart, Category.assoc, globalDividedTensorChart_structure]
  exact WeierstrassDilatation.residueNodeIso_structure ..

/-- Normalization loses no points of the complete terminal divided tensor chart. -/
theorem terminalNodeChart_range :
    Set.range (terminalNodeChart hπ data D j hj hk0 hk hp) =
      Set.range (globalDividedTensorChart hπ data K j hj) := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(e).hom p, rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(e).inv p, ?_⟩
    have he : (e).hom ((e).inv p) = p :=
      congrArg (fun f => f p) (e).inv_hom_id
    change globalDividedTensorChart hπ data K j hj ((e).hom ((e).inv p)) = _
    rw [he]
end Node

end FLT.Mazur.WeierstrassDividedDepth
