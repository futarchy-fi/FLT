/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticExtensionChartClosure
public import FLT.Mazur.EllipticSubgroupClosedFiberPoints

/-!
# Quasi-finiteness for the transported prime-order subgroup

Apply the actual Y/Z gluing and finite-fiber theorem to the subgroup obtained
from field extension and the generic variable change. Its finiteness is proved
from the transported generator's order, without an integral model assumption.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur

open WeierstrassCurve

variable {R K L : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [DecidableEq K] [DecidableEq L]
  (A : ValuationSubring L) (W : WeierstrassCurve R) (U : WeierstrassCurve A)
  [(W.map (algebraMap R L)).IsElliptic] (C : VariableChange L)
  (hC : C • W.map (algebraMap R L) = U.map (algebraMap A L))
  (P : (W.map (algebraMap R K)).toAffine.Point)

/-- The transported prime subgroup's actual glued closure is locally quasi-finite. -/
theorem ellipticExtensionClosure_locallyQuasiFinite {p : ℕ} [Fact p.Prime]
    (hP : p • P = 0) (hP0 : P ≠ 0) :
    LocallyQuasiFinite (EllipticSubgroupChart.closureToBase A U
      (ellipticExtensionProjectiveSubgroup A W U C hC P) 1 2) := by
  let _ := Nat.finite_of_card_ne_zero
    ((ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0).trans_ne
      (Fact.out : p.Prime).ne_zero)
  infer_instance

/-- Every fiber of this concrete closure is a finite set of scheme points. -/
theorem ellipticExtensionClosure_finite_fiber {p : ℕ} [Fact p.Prime]
    (hP : p • P = 0) (hP0 : P ≠ 0) (x : Spec (.of A)) :
    (EllipticSubgroupChart.closureToBase A U
      (ellipticExtensionProjectiveSubgroup A W U C hC P) 1 2 ⁻¹' {x}).Finite := by
  let _ := ellipticExtensionClosure_locallyQuasiFinite A W U C hC P hP hP0
  exact Scheme.Hom.finite_preimage_singleton _ x

end FLT.Mazur
