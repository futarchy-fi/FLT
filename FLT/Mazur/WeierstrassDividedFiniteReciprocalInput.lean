/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairReciprocalGeometry
public import FLT.Mazur.WeierstrassDividedFiniteSecantInput

/-!
# Two divided reciprocal inputs in the same entire finite model

Embed the new reciprocal domain into the product of the actual finite projective
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
local notation "T" => WeierstrassDilatation.DividedPairReciprocalOutputRing W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R H))

/-- The new reciprocal input is a genuine open of the product of the whole modified model. -/
def finiteReciprocalInput : Spec (.of T) ⟶ pullback base base :=
  WeierstrassDilatation.dividedPairReciprocalOutputToProduct W s (d).b3 (d).b4 (d).b6 ≫
    finiteSecantPairChart hπ data j hj

instance finiteReciprocalInput_open : IsOpenImmersion (finiteReciprocalInput hπ data j hj) := by
  unfold finiteReciprocalInput
  infer_instance

/-- The first input remains the exact first divided point in the original cubic. -/
@[reassoc] theorem finiteReciprocalInput_fst_contraction :
    finiteReciprocalInput hπ data j hj ≫ pullback.fst base base ≫
        finiteGlobalContraction hπ data j hj =
      WeierstrassDilatation.dividedPairReciprocalOutputToProduct W s (d).b3 (d).b4 (d).b6 ≫
        pullback.fst q q ≫ toCurve d := by
  simp only [finiteReciprocalInput, finiteSecantPairChart, Category.assoc,
    pullback.map, pullback.lift_fst_assoc, finiteSecantDividedChart_contraction]

/-- The second input remains the exact second divided point in the original cubic. -/
@[reassoc] theorem finiteReciprocalInput_snd_contraction :
    finiteReciprocalInput hπ data j hj ≫ pullback.snd base base ≫
        finiteGlobalContraction hπ data j hj =
      WeierstrassDilatation.dividedPairReciprocalOutputToProduct W s (d).b3 (d).b4 (d).b6 ≫
        pullback.snd q q ≫ toCurve d := by
  simp only [finiteReciprocalInput, finiteSecantPairChart, Category.assoc,
    pullback.map, pullback.lift_snd_assoc, finiteSecantDividedChart_contraction]

/-- Both inputs retain the original coefficient map of the universal reciprocal source. -/
@[reassoc] theorem finiteReciprocalInput_structure :
    finiteReciprocalInput hπ data j hj ≫ pullback.fst base base ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  simp only [finiteReciprocalInput, finiteSecantPairChart, Category.assoc,
    pullback.map, pullback.lift_fst_assoc, finiteSecantDividedChart_structure,
    WeierstrassDilatation.dividedPairReciprocalOutputToProduct_fst_assoc,
    WeierstrassIntegralChart.specAlgHom_structure]

end FLT.Mazur.WeierstrassDividedDepth
