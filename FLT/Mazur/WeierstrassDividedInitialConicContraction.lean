/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialConicParameters
public import FLT.Mazur.WeierstrassModificationXResidueConicContraction

/-!
# The original conic and its two parameters retain the original nodal contraction

These are equalities of complete affine component morphisms into the original
cubic, retaining the actual divided coefficient and both original parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassModificationX
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
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "g" => finiteGlobalStructure hπ data j hj
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap K (ConicParameterOpen c)))

/-- The original integral cubic node, with its actual residue coefficients. -/
def initialOriginalCubicNode : Spec (.of K) ⟶ integralCurve W :=
  Spec.map (CommRingCat.ofHom
    (residueOriginMap D start hstart (Data.b6 d) (Data.factor6 d)).toRingHom) ≫
      integralCurveChart W 2

omit [IsBezout R] [IsDomain R] in
/-- The original node has exactly the original integral-to-residue structure map. -/
@[reassoc] theorem initialOriginalCubicNode_base :
    initialOriginalCubicNode data D hstart ≫ integralCurveStructure W = q := by
  rw [initialOriginalCubicNode, Category.assoc, integralCurveChart_structure,
    chartStructure, specAlgHom_structure]

/-- The entire retained conic contracts to the actual original cubic node. -/
@[reassoc] theorem initialGlobalConic_contraction :
    initialGlobalConic hπ data D j hj hstart hk ≫ pullback.snd q g ≫
        finiteGlobalContraction hπ data j hj =
      conicStructure a c ≫ initialOriginalCubicNode data D hstart := by
  rw [initialGlobalConic, initialGlobalResidueFiberChart]
  simp only [Category.assoc, globalInitialTensorChart_toCurve]
  change residueConicImmersion D start hstart hk (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) ≫ residueChartContraction start
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
        (Data.factor6 d) = _
  exact residueConic_contraction D start hstart hk (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The first full exceptional parameter retains that same original nodal contraction. -/
@[reassoc] theorem initialGlobalConicFirstParameter_contraction :
    initialGlobalConicFirstParameter hπ data D j hj hstart hk ≫ pullback.snd q g ≫
        finiteGlobalContraction hπ data j hj = b ≫ initialOriginalCubicNode data D hstart := by
  calc
    _ = initialGlobalConicFirstParameter hπ data D j hj hstart hk ≫
        pullback.fst q g ≫ initialOriginalCubicNode data D hstart := by
      simp only [initialGlobalConicFirstParameter, Category.assoc,
        initialGlobalConic_contraction, initialGlobalConic_structure_assoc]
    _ = _ := by rw [initialGlobalConicFirstParameter_structure_assoc]

/-- The opposite full exceptional parameter retains the same node and coefficient map. -/
@[reassoc] theorem initialGlobalConicSecondParameter_contraction :
    initialGlobalConicSecondParameter hπ data D j hj hstart hk ≫ pullback.snd q g ≫
        finiteGlobalContraction hπ data j hj = b ≫ initialOriginalCubicNode data D hstart := by
  calc
    _ = initialGlobalConicSecondParameter hπ data D j hj hstart hk ≫
        pullback.fst q g ≫ initialOriginalCubicNode data D hstart := by
      simp only [initialGlobalConicSecondParameter, Category.assoc,
        initialGlobalConic_contraction, initialGlobalConic_structure_assoc]
    _ = _ := by rw [initialGlobalConicSecondParameter_structure_assoc]

end FLT.Mazur.WeierstrassDividedDepth
