/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationZeroResidueGeometry
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedGlobalTensorAtlas
public import FLT.Mazur.WeierstrassDividedTensorAtlasComparison

/-!
# The full terminal nodal chart at divided depth zero

When start+j=0, the terminal divided tensor chart is the original nodal
affine cubic. Its actual global inclusion, complete image, coefficient
structure, contraction and exact atlas index are retained.
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
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth)
  (j : ℕ) (hj : j ≤ n) (hzero : start + j = 0)
open WeierstrassDilatation
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "N" => WeierstrassIntegralChart.splitNodalEquation (residueTangentUnit D)
local notation "A" => WeierstrassIntegralChart.Coordinate N 2
local notation "e" => zeroResidueNodalIso D hdepth (start + j) hzero
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The whole zero-depth nodal affine chart as an open of the actual projective residue model. -/
def terminalZeroNodalChart : Spec (.of A) ⟶ finiteGlobalTensorModel hπ data K j hj :=
  (e).hom ≫ globalDividedTensorChart hπ data K j hj

instance terminalZeroNodalChart_isOpenImmersion :
    IsOpenImmersion (terminalZeroNodalChart hπ data D hdepth j hj hzero) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The nodal chart covers the whole original terminal tensor chart. -/
theorem terminalZeroNodalChart_range :
    Set.range (terminalZeroNodalChart hπ data D hdepth j hj hzero) =
      Set.range (globalDividedTensorChart hπ data K j hj) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(e).hom x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (e).hom.homeomorph.surjective x
    exact ⟨y, congrArg (globalDividedTensorChart hπ data K j hj) hy⟩

/-- The full zero-depth terminal comparison retains every original cubic function. -/
@[reassoc] theorem terminalZeroNodalChart_toCurve :
    terminalZeroNodalChart hπ data D hdepth j hj hzero ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj = zeroResidueNodalContraction D hdepth := by
  rw [terminalZeroNodalChart, Category.assoc, globalDividedTensorChart_toCurve]
  exact zeroResidueNodalIso_contraction D hdepth (start + j) hzero
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The actual terminal nodal chart retains its residue coefficient structure. -/
@[reassoc] theorem terminalZeroNodalChart_structure :
    terminalZeroNodalChart hπ data D hdepth j hj hzero ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  rw [terminalZeroNodalChart, Category.assoc, globalDividedTensorChart_structure]
  exact zeroResidueNodalIso_structure D hdepth (start + j) hzero
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The full nodal normalization identifies the exact first noninfinity atlas object. -/
def terminalZeroNodalAtlasIso : Spec (.of A) ≅ globalTensorAtlasObject hπ data K j hj 1 :=
  e ≪≫ finiteDividedTensorAtlasIso hπ data K j hj

/-- The indexed comparison retains the original projective terminal inclusion. -/
@[reassoc] theorem terminalZeroNodalAtlasIso_map :
    (terminalZeroNodalAtlasIso hπ data D hdepth j hj hzero).hom ≫
      globalTensorAtlasMap hπ data K j hj 1 =
        terminalZeroNodalChart hπ data D hdepth j hj hzero := by
  change (_ ≫ _) ≫ (finiteTensorAtlasMap hπ data K j hj 0 ≫ _) = _
  rw [Category.assoc, ← Category.assoc (finiteDividedTensorAtlasIso hπ data K j hj).hom,
    finiteDividedTensorAtlasIso_map]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
