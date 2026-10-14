/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteNodeBoundarySection
public import FLT.Mazur.WeierstrassDividedOlderGlobalStep

/-!
# Integral retained presentations of original shallower primitive points

The horizontal boundary at a point's primitive depth embeds through the
successive chart into every later finite model. Its contraction is unchanged,
so its integral section equals the unrestricted proper extension there.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

/-- The whole primitive-depth horizontal open retained in any later global model. -/
def finiteRetainedBoundaryChart : boundary d ⟶ finiteGlobalModel hπ data (j + 1 + r) hr :=
  previousToX hπ d e ≫ olderGlobalChart hπ data j hj r hr

instance finiteRetainedBoundaryChart_isOpenImmersion :
    IsOpenImmersion (finiteRetainedBoundaryChart A hπ data j hj r hr) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Retention preserves the complete original cubic contraction of the horizontal boundary. -/
@[reassoc] theorem finiteRetainedBoundaryChart_contraction :
    finiteRetainedBoundaryChart A hπ data j hj r hr ≫
      finiteGlobalContraction hπ data (j + 1 + r) hr = boundaryInclusion d ≫ toCurve d := by
  rw [finiteRetainedBoundaryChart, olderGlobalChart, Category.assoc, Category.assoc,
    finiteLocalChart_contraction, olderSuccessiveChart_toCurve,
    previousToX_contraction_assoc]

/-- The whole retained boundary has its original integral coefficient structure. -/
@[reassoc] theorem finiteRetainedBoundaryChart_structure :
    finiteRetainedBoundaryChart A hπ data j hj r hr ≫
      finiteGlobalStructure hπ data (j + 1 + r) hr =
        boundaryInclusion d ≫ toCurve d ≫ WeierstrassIntegralChart.integralCurveStructure W := by
  change _ ≫ finiteGlobalContraction hπ data (j + 1 + r) hr ≫ _ = _
  rw [← Category.assoc, finiteRetainedBoundaryChart_contraction, Category.assoc]

variable {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)

/-- The original primitive section presented inside every later retained chart. -/
def finiteRetainedNodeSection : Spec (.of A) ⟶ finiteGlobalModel hπ data (j + 1 + r) hr :=
  finiteNodeBoundarySection A hπ data D j (Nat.le_of_succ_le hj) hk0 hp P v hv ≫
    finiteRetainedBoundaryChart A hπ data j hj r hr

/-- The retained integral presentation contracts to exactly the original integral point. -/
@[reassoc] theorem finiteRetainedNodeSection_contraction :
    finiteRetainedNodeSection A hπ data j hj r hr D hk0 hp P v hv ≫
      finiteGlobalContraction hπ data (j + 1 + r) hr =
        WeierstrassIntegralChart.integralPointSection A W P := by
  rw [finiteRetainedNodeSection, Category.assoc, finiteRetainedBoundaryChart_contraction,
    finiteNodeBoundarySection_toCurve]

/-- Uniqueness identifies the retained presentation with the actual unrestricted extension. -/
theorem finiteRetainedNodeSection_eq :
    finiteRetainedNodeSection A hπ data j hj r hr D hk0 hp P v hv =
      finitePointSection A hπ data (j + 1 + r) hr P :=
  finitePointSection_unique_of_contraction A hπ data (j + 1 + r) hr P _
    (finiteRetainedNodeSection_contraction A hπ data j hj r hr D hk0 hp P v hv)

include D hk0 hp v hv in
/-- The full integral section lies in the retained open, including its closed point. -/
theorem finitePointSection_mem_retainedBoundary (z : Spec (.of A)) :
    finitePointSection A hπ data (j + 1 + r) hr P z ∈
      Set.range (finiteRetainedBoundaryChart A hπ data j hj r hr) := by
  rw [← finiteRetainedNodeSection_eq A hπ data j hj r hr D hk0 hp P v hv]
  exact ⟨_, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
