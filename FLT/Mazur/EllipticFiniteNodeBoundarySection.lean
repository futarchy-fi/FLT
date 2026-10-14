/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteDividedPointSection
public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# Primitive points below middle depth have integral horizontal sections

The actual divided x-coordinate is a unit for a primitive point strictly
below middle depth. Localization therefore gives an integral section of the
horizontal boundary, which can be retained through subsequent modifications.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "ev" => finiteNodePointEvaluation A hπ data j hj P v hv
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "B" => WeierstrassDilatation.HorizontalCoordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)

include D hk0 hp hv in
/-- Primitivity and the strict depth bound force the original divided x to be a unit. -/
theorem finiteNodePoint_horizontal_unit : IsUnit (ev x) := by
  have he := node_point_branches_below_middle W hπ D.maximalIdeal_eq depth v.depth
    (by omega) (by omega) D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    v.a v.b v.primitive v.equation
  change IsUnit (WeierstrassDilatation.evaluation W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) v.a v.b _ x)
  rw [WeierstrassDilatation.evaluation_x]
  exact he.1

/-- The primitive coordinates extend to the actual integral horizontal localization. -/
def finiteNodeBoundaryEvaluation : B →ₐ[A] A :=
  IsLocalization.Away.liftAlgHom (f := ev) x
    (finiteNodePoint_horizontal_unit A hπ data D j hj hk0 hp P v hv)

/-- Localization retains every original divided coordinate. -/
theorem finiteNodeBoundaryEvaluation_base (z) :
    finiteNodeBoundaryEvaluation A hπ data D j hj hk0 hp P v hv (algebraMap _ B z) =
      ev z := by
  rw [finiteNodeBoundaryEvaluation, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The actual integral horizontal section of the original primitive point. -/
def finiteNodeBoundarySection : Spec (.of A) ⟶ boundary d :=
  Spec.map (CommRingCat.ofHom
    (finiteNodeBoundaryEvaluation A hπ data D j hj hk0 hp P v hv).toRingHom)

/-- The boundary section includes as the original divided evaluation, on every function. -/
@[reassoc] theorem finiteNodeBoundarySection_inclusion :
    finiteNodeBoundarySection A hπ data D j hj hk0 hp P v hv ≫ boundaryInclusion d =
      Spec.map (CommRingCat.ofHom (ev).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact finiteNodeBoundaryEvaluation_base A hπ data D j hj hk0 hp P v hv

/-- Its original cubic contraction is the integral section of the given generic point. -/
@[reassoc] theorem finiteNodeBoundarySection_toCurve :
    finiteNodeBoundarySection A hπ data D j hj hk0 hp P v hv ≫
      boundaryInclusion d ≫ toCurve d =
        WeierstrassIntegralChart.integralPointSection A W P := by
  have hc : finiteDividedGlobalChart hπ data j hj ≫
      finiteGlobalContraction hπ data j hj = toCurve d :=
    finiteDividedGlobalChart_cubic hπ data j hj
  rw [← Category.assoc, finiteNodeBoundarySection_inclusion, ← hc, ← Category.assoc,
    finitePointSection_nodeChart, finitePointSection_contraction]

end FLT.Mazur.WeierstrassDividedDepth
