/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairTangentGeometry
public import FLT.Mazur.WeierstrassDividedFiniteSecantInput

/-!
# Two divided tangent inputs in the same entire finite model

Embed the new tangent domain into the product of the actual finite projective
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
local notation "s" => π ^ (start + j)
local notation "H" => WeierstrassDilatation.Coordinate W s (d).b3 (d).b4 (d).b6
local notation "T" => WeierstrassDilatation.DividedPairTangentRing W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R H))

/-- The new tangent input is a genuine open of the product of the whole modified model. -/
def finiteTangentInput : Spec (.of T) ⟶ pullback base base :=
  WeierstrassDilatation.dividedPairTangentToProduct W s (d).b3 (d).b4 (d).b6 ≫
    finiteSecantPairChart hπ data j hj

instance finiteTangentInput_open : IsOpenImmersion (finiteTangentInput hπ data j hj) := by
  unfold finiteTangentInput
  infer_instance

/-- The first input remains the exact first divided point in the original cubic. -/
@[reassoc] theorem finiteTangentInput_fst_contraction :
    finiteTangentInput hπ data j hj ≫ pullback.fst base base ≫
        finiteGlobalContraction hπ data j hj =
      WeierstrassDilatation.dividedPairTangentToProduct W s (d).b3 (d).b4 (d).b6 ≫
        pullback.fst q q ≫ toCurve d := by
  simp only [finiteTangentInput, finiteSecantPairChart, Category.assoc,
    pullback.map, pullback.lift_fst_assoc, finiteSecantDividedChart_contraction]

/-- The second input remains the exact second divided point in the original cubic. -/
@[reassoc] theorem finiteTangentInput_snd_contraction :
    finiteTangentInput hπ data j hj ≫ pullback.snd base base ≫
        finiteGlobalContraction hπ data j hj =
      WeierstrassDilatation.dividedPairTangentToProduct W s (d).b3 (d).b4 (d).b6 ≫
        pullback.snd q q ≫ toCurve d := by
  simp only [finiteTangentInput, finiteSecantPairChart, Category.assoc,
    pullback.map, pullback.lift_snd_assoc, finiteSecantDividedChart_contraction]

/-- Both inputs retain the original coefficient map of the universal tangent source. -/
@[reassoc] theorem finiteTangentInput_structure :
    finiteTangentInput hπ data j hj ≫ pullback.fst base base ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  simp only [finiteTangentInput, finiteSecantPairChart, Category.assoc,
    pullback.map, pullback.lift_fst_assoc, finiteSecantDividedChart_structure,
    WeierstrassDilatation.dividedPairTangentToProduct_fst_assoc,
    WeierstrassIntegralChart.specAlgHom_structure]

end FLT.Mazur.WeierstrassDividedDepth
