/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedLaurentPoints

/-!
# Laurent charts in every later original finite model

Both original punctures are retained as coefficient-preserving open immersions.
Their tangent-unit evaluations recover the unrestricted proper specialization
at every later stage, without replacing the original finite model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
local notation "F" => ResidueField A
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "c" => finiteRetainedBoundaryTensorChart A hπ data j hj r hr F
local notation "base" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A F)))
  (finiteGlobalStructure hπ data (j + 1 + r) hr)

/-- The actual negative puncture retained in the later original finite model. -/
def retainedNegativeLaurentChart : Spec (.of F[T;T⁻¹]) ⟶
    finiteGlobalTensorModel hπ data F (j + 1 + r) hr :=
  WeierstrassDilatation.residueHorizontalLeft D (start + j) hk0 (by omega)
    (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp ≫ c

/-- The actual positive puncture retained in the later original finite model. -/
def retainedPositiveLaurentChart : Spec (.of F[T;T⁻¹]) ⟶
    finiteGlobalTensorModel hπ data F (j + 1 + r) hr :=
  WeierstrassDilatation.residueHorizontalRight D (start + j) hk0 (by omega)
    (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp ≫ c

instance retainedNegativeLaurentChart_isOpenImmersion :
    IsOpenImmersion (retainedNegativeLaurentChart A hπ data D j hj r hr hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance retainedPositiveLaurentChart_isOpenImmersion :
    IsOpenImmersion (retainedPositiveLaurentChart A hπ data D j hj r hr hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Retaining the negative puncture leaves its original coefficient projection unchanged. -/
@[reassoc] theorem retainedNegativeLaurentChart_structure :
    retainedNegativeLaurentChart A hπ data D j hj r hr hk0 hp ≫ base =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [retainedNegativeLaurentChart, Category.assoc, finiteRetainedBoundaryTensorChart_structure,
    WeierstrassDilatation.residueHorizontalLeft_structure]

/-- Retaining the positive puncture leaves its original coefficient projection unchanged. -/
@[reassoc] theorem retainedPositiveLaurentChart_structure :
    retainedPositiveLaurentChart A hπ data D j hj r hr hk0 hp ≫ base =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [retainedPositiveLaurentChart, Category.assoc, finiteRetainedBoundaryTensorChart_structure,
    WeierstrassDilatation.residueHorizontalRight_structure]

variable (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)

include hv in
/-- The retained negative Laurent point is the full later proper specialization. -/
theorem finitePointSpecialization_retained_negative_laurent (hb : IsUnit v.b) :
    Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := F) (nodeNegativeLaurentUnit A P v hb)).toRingHom) ≫
      retainedNegativeLaurentChart A hπ data D j hj r hr hk0 hp =
        finitePointSpecialization A hπ data (j + 1 + r) hr P := by
  rw [retainedNegativeLaurentChart, ← Category.assoc,
    finiteNodeBoundaryEvaluation_negative_laurent A hπ data D j
      (Nat.le_of_succ_le hj) hk0 (by omega) hp P v hv hb,
    finiteCoefficientPointSection_retainedChart]
  rfl

include hv in
/-- The retained positive Laurent point is the full later proper specialization. -/
theorem finitePointSpecialization_retained_positive_laurent
    (hb : IsUnit (v.b + W.a₁ * v.a)) :
    Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := F) (nodePositiveLaurentUnit A P v hb)).toRingHom) ≫
      retainedPositiveLaurentChart A hπ data D j hj r hr hk0 hp =
        finitePointSpecialization A hπ data (j + 1 + r) hr P := by
  rw [retainedPositiveLaurentChart, ← Category.assoc,
    finiteNodeBoundaryEvaluation_positive_laurent A hπ data D j
      (Nat.le_of_succ_le hj) hk0 (by omega) hp P v hv hb,
    finiteCoefficientPointSection_retainedChart]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
