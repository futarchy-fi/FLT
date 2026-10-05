/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticExtensionClosureFinite
public import FLT.Mazur.EllipticSubgroupGlobalRank

/-!
# Exact rank of the transported prime subgroup closure

The actual generic evaluation is an equivalence with the point algebra of the
transported subgroup. Its cardinality p gives generic rank p, and integral
rank p over a DVR. The integral group operations remain a separate construction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve
open scoped TensorProduct

variable {R K L : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [DecidableEq K] [DecidableEq L]
  (A : ValuationSubring L) (W : WeierstrassCurve R) (U : WeierstrassCurve A)
  [(W.map (algebraMap R L)).IsElliptic] (C : VariableChange L)
  (hC : C • W.map (algebraMap R L) = U.map (algebraMap A L))
  (P : (W.map (algebraMap R K)).toAffine.Point)

/-- The actual transported subgroup closure has the prescribed split generic algebra. -/
def ellipticExtensionClosureGenericEquiv {p : ℕ} [Fact p.Prime]
    (hP : p • P = 0) (hP0 : P ≠ 0) :
    L ⊗[A] EllipticSubgroupChart.GlobalClosure A U
      (ellipticExtensionProjectiveSubgroup A W U C hC P) ≃ₐ[L]
        (ellipticExtensionProjectiveSubgroup A W U C hC P → L) := by
  let _ := Nat.finite_of_card_ne_zero
    ((ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0).trans_ne
      (Fact.out : p.Prime).ne_zero)
  exact EllipticSubgroupChart.globalClosureGenericEquiv A U
    (ellipticExtensionProjectiveSubgroup A W U C hC P)

/-- The transported prime subgroup closure has generic rank p. -/
theorem ellipticExtensionClosure_generic_finrank {p : ℕ} [Fact p.Prime]
    (hP : p • P = 0) (hP0 : P ≠ 0) :
    Module.finrank L (L ⊗[A] EllipticSubgroupChart.GlobalClosure A U
      (ellipticExtensionProjectiveSubgroup A W U C hC P)) = p := by
  let _ := Nat.finite_of_card_ne_zero
    ((ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0).trans_ne
      (Fact.out : p.Prime).ne_zero)
  exact (EllipticSubgroupChart.globalClosure_generic_finrank A U
    (ellipticExtensionProjectiveSubgroup A W U C hC P)).trans
      (ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0)

/-- Over a DVR the actual finite flat prime subgroup closure has integral rank p. -/
theorem ellipticExtensionClosure_finrank [IsDedekindDomain A] {p : ℕ} [Fact p.Prime]
    (hP : p • P = 0) (hP0 : P ≠ 0) :
    Module.finrank A (EllipticSubgroupChart.GlobalClosure A U
      (ellipticExtensionProjectiveSubgroup A W U C hC P)) = p := by
  let _ := Nat.finite_of_card_ne_zero
    ((ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0).trans_ne
      (Fact.out : p.Prime).ne_zero)
  exact (EllipticSubgroupChart.globalClosure_finrank A U
    (ellipticExtensionProjectiveSubgroup A W U C hC P)).trans
      (ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0)

end FLT.Mazur
