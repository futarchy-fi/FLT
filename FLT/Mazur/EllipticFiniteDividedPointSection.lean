/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFinitePointSectionAction
public import FLT.Mazur.WeierstrassDividedChartCubicAction
public import FLT.Mazur.EllipticDilatationPointSection

/-!
# The proper extension retains the original primitive nodal coordinates

A section contracting to the original cubic section is the unique proper
extension. In particular primitive coordinates at the named divided depth
compute that extension inside the actual finite global chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "C" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A K))
local notation "c" => finiteGlobalContraction hπ data j hj

/-- The original contraction determines the whole proper section, even outside E₀. -/
theorem finitePointSection_unique_of_contraction
    (P : (W.map (algebraMap A K)).toProjective.Point)
    (t : Spec (.of A) ⟶ finiteGlobalModel hπ data j hj)
    (ht : t ≫ c = integralPointSection A W P) :
    t = finitePointSection A hπ data j hj P := by
  apply finitePointSection_unique A hπ data j hj P
  · change t ≫ c ≫ integralCurveStructure W = _
    rw [← Category.assoc, ht, integralPointSection_structure]
  · apply finiteGlobal_eq_smoothEmbedding hπ data j hj
    rw [Category.assoc, ht, integralPointSection_generic, projectiveToSmooth_inclusion]

variable (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)

include hπ hv in
/-- The primitive coordinates solve the equation of the actual indexed divided chart. -/
theorem finiteNodePoint_equation :
    v.b ^ 2 + (algebraMap A A W.a₁ * v.a + algebraMap A A (Data.b3 d)) * v.b =
      algebraMap A A (π ^ (start + j)) * v.a ^ 3 + algebraMap A A W.a₂ * v.a ^ 2 +
        algebraMap A A (Data.b4 d) * v.a + algebraMap A A (Data.b6 d) := by
  have h := WeierstrassDilatation.nodePoint_divided_equation A W hπ v
    (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (by simpa only [hv] using (Data.factor3 d)) (by simpa only [hv] using (Data.factor4 d))
    (by simpa only [hv] using (Data.factor6 d))
  simpa only [hv] using h

/-- Evaluation of the original primitive point on the actual indexed divided algebra. -/
def finiteNodePointEvaluation : C →ₐ[A] A :=
  WeierstrassDilatation.evaluation W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
      v.a v.b
    (finiteNodePoint_equation A hπ data j hj P v hv)

/-- The divided chart evaluation is exactly the proper section of the same original point. -/
theorem finitePointSection_nodeChart :
    Spec.map (CommRingCat.ofHom (finiteNodePointEvaluation A hπ data j hj P v hv).toRingHom) ≫
        finiteDividedGlobalChart hπ data j hj = finitePointSection A hπ data j hj P := by
  apply finitePointSection_unique_of_contraction A hπ data j hj P
  rw [Category.assoc, finiteDividedGlobalChart_cubic]
  change Spec.map (CommRingCat.ofHom
    (WeierstrassDilatation.evaluation W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
      v.a v.b
      (finiteNodePoint_equation A hπ data j hj P v hv)).toRingHom) ≫
    WeierstrassDilatation.toCurve W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) = _
  have he := WeierstrassDilatation.nodePoint_projective_equation A W v
  have hr := WeierstrassDilatation.nodePoint_projective_represents A W v
  rw [hv] at he hr
  rw [WeierstrassDilatation.evaluation_toCurve W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
    v.a v.b _ he]
  exact (integralPointSection_chart A W P 2 _ he rfl hr).symm

end FLT.Mazur.WeierstrassDividedDepth
