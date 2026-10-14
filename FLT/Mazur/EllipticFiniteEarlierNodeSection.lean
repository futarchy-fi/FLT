/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteDividedPointSection

/-!
# Original nodal coordinates at every earlier divided stage

A primitive point of depth at least the chart index evaluates the actual
chart at its scaled divided coordinates. Contraction identifies this section
with the original proper extension, without requiring primitivity at that index.
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

variable (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : start + j ≤ v.depth)
local notation "a" => π ^ (v.depth - (start + j)) * v.a
local notation "b" => π ^ (v.depth - (start + j)) * v.b

include hv in
/-- Scaling earlier divided coordinates recovers the original affine coordinates. -/
theorem finiteEarlierNode_scaled (x : A) :
    π ^ (start + j) * (π ^ (v.depth - (start + j)) * x) = π ^ v.depth * x := by
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hv]

include hv in
/-- The earlier divided coordinates still solve the original projective equation. -/
theorem finiteEarlierNode_projective_equation :
    (W.map (algebraMap A A)).toProjective.Equation
      ![π ^ (start + j) * a, π ^ (start + j) * b, 1] := by
  rw [finiteEarlierNode_scaled A j P v hv,
    finiteEarlierNode_scaled A j P v hv]
  exact WeierstrassDilatation.nodePoint_projective_equation A W v

include hπ hv in
/-- The scaled coordinates solve the actual earlier divided chart equation. -/
theorem finiteEarlierNode_equation :
    b ^ 2 + (algebraMap A A W.a₁ * a + algebraMap A A (Data.b3 d)) * b =
      algebraMap A A (π ^ (start + j)) * a ^ 3 + algebraMap A A W.a₂ * a ^ 2 +
        algebraMap A A (Data.b4 d) * a + algebraMap A A (Data.b6 d) := by
  apply WeierstrassDilatation.equation_of_scaled W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
    (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ))
  exact finiteEarlierNode_projective_equation A j P v hv

/-- Evaluation on an earlier chart, retaining the exact original point. -/
def finiteEarlierNodeEvaluation : C →ₐ[A] A :=
  WeierstrassDilatation.evaluation W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
    a b (finiteEarlierNode_equation A hπ data j hj P v hv)

/-- This earlier chart section is the actual proper extension. -/
theorem finitePointSection_earlierNodeChart :
    Spec.map (CommRingCat.ofHom
        (finiteEarlierNodeEvaluation A hπ data j hj P v hv).toRingHom) ≫
      finiteDividedGlobalChart hπ data j hj = finitePointSection A hπ data j hj P := by
  apply finitePointSection_unique_of_contraction A hπ data j hj P
  rw [Category.assoc, finiteDividedGlobalChart_cubic]
  change Spec.map (CommRingCat.ofHom
    (WeierstrassDilatation.evaluation W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
      a b (finiteEarlierNode_equation A hπ data j hj P v hv)).toRingHom) ≫
    WeierstrassDilatation.toCurve W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) = _
  rw [WeierstrassDilatation.evaluation_toCurve W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
    a b _ (finiteEarlierNode_projective_equation A j P v hv)]
  apply (integralPointSection_chart A W P 2 _ _ rfl ?_).symm
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [finiteEarlierNode_scaled A j P v hv,
    finiteEarlierNode_scaled A j P v hv]
  exact WeierstrassDilatation.nodePoint_projective_represents A W v

end FLT.Mazur.WeierstrassDividedDepth
