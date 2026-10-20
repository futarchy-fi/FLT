/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairSecantGeometry
public import FLT.Mazur.WeierstrassDividedGlobalFiniteFlat

/-!
# Two divided secant inputs in the same entire finite model

Embed the new secant domain into the product of the actual finite projective
model with itself. Both projections retain their original divided chart and
original cubic contraction; no original-smooth input is imposed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "E₀" => initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)
local notation "s" => π ^ (start + j)
local notation "H" => WeierstrassDilatation.Coordinate W s (d).b3 (d).b4 (d).b6
local notation "T" => WeierstrassDilatation.DividedPairSecantRing W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R H))

/-- The final divided chart inside the actual entire finite projective model. -/
def finiteSecantDividedChart : chart d ⟶ finiteGlobalModel hπ data j hj :=
  (finiteExterior hπ data E₀ j hj).dividedChart ≫ finiteLocalChart hπ data j hj

instance finiteSecantDividedChart_open :
    IsOpenImmersion (finiteSecantDividedChart hπ data j hj) := by
  unfold finiteSecantDividedChart
  infer_instance

/-- The chart retains the precise original divided contraction. -/
@[reassoc] theorem finiteSecantDividedChart_contraction :
    finiteSecantDividedChart hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      toCurve d := finiteGlobal_divided_contraction hπ data j hj

/-- The chart has exactly the original coefficient structure. -/
@[reassoc] theorem finiteSecantDividedChart_structure :
    finiteSecantDividedChart hπ data j hj ≫ base = q := by
  rw [finiteGlobalStructure, finiteSecantDividedChart_contraction_assoc, toCurve_structure]

/-- The entire divided pair chart maps openly into the entire finite-model product. -/
def finiteSecantPairChart : pullback q q ⟶ pullback base base :=
  pullback.map q q base base (finiteSecantDividedChart hπ data j hj)
    (finiteSecantDividedChart hπ data j hj) (𝟙 _) (by
      rw [Category.comp_id, finiteSecantDividedChart_structure]) (by
      rw [Category.comp_id, finiteSecantDividedChart_structure])

instance finiteSecantPairChart_open : IsOpenImmersion (finiteSecantPairChart hπ data j hj) := by
  unfold finiteSecantPairChart
  infer_instance

/-- The new secant input is a genuine open of the product of the whole modified model. -/
def finiteSecantInput : Spec (.of T) ⟶ pullback base base :=
  WeierstrassDilatation.dividedPairSecantToProduct W s (d).b3 (d).b4 (d).b6 ≫
    finiteSecantPairChart hπ data j hj

instance finiteSecantInput_open : IsOpenImmersion (finiteSecantInput hπ data j hj) := by
  unfold finiteSecantInput
  infer_instance

/-- The first input remains the exact first divided point in the original cubic. -/
@[reassoc] theorem finiteSecantInput_fst_contraction :
    finiteSecantInput hπ data j hj ≫ pullback.fst base base ≫
        finiteGlobalContraction hπ data j hj =
      WeierstrassDilatation.dividedPairSecantToProduct W s (d).b3 (d).b4 (d).b6 ≫
        pullback.fst q q ≫ toCurve d := by
  simp only [finiteSecantInput, finiteSecantPairChart, Category.assoc,
    pullback.map, pullback.lift_fst_assoc, finiteSecantDividedChart_contraction]

/-- The second input remains the exact second divided point in the original cubic. -/
@[reassoc] theorem finiteSecantInput_snd_contraction :
    finiteSecantInput hπ data j hj ≫ pullback.snd base base ≫
        finiteGlobalContraction hπ data j hj =
      WeierstrassDilatation.dividedPairSecantToProduct W s (d).b3 (d).b4 (d).b6 ≫
        pullback.snd q q ≫ toCurve d := by
  simp only [finiteSecantInput, finiteSecantPairChart, Category.assoc,
    pullback.map, pullback.lift_snd_assoc, finiteSecantDividedChart_contraction]

/-- Both inputs retain the original coefficient map of the universal secant source. -/
@[reassoc] theorem finiteSecantInput_structure :
    finiteSecantInput hπ data j hj ≫ pullback.fst base base ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  simp only [finiteSecantInput, finiteSecantPairChart, Category.assoc,
    pullback.map, pullback.lift_fst_assoc, finiteSecantDividedChart_structure,
    WeierstrassDilatation.dividedPairSecantToProduct_fst_assoc,
    WeierstrassIntegralChart.specAlgHom_structure]

end FLT.Mazur.WeierstrassDividedDepth
