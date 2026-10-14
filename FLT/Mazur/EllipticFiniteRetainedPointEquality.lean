/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedSpecialization
public import FLT.Mazur.WeierstrassDilatationHorizontalPointExt

/-!
# Equality of actual retained specializations

For primitive points at the same strict depth, equality in every later finite
model is exactly equality of the two original divided residues. The proof
uses the actual retained open immersion and localization evaluation.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
  (P Q : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
  (w : NodePointCoordinates A W π Q) (hw : w.depth = start + j)
local notation "F" => ResidueField A
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "B" => WeierstrassDilatation.HorizontalCoordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b₁" => finiteNodeBoundaryEvaluation A hπ data D j
  (Nat.le_of_succ_le hj) hk0 hp P v hv
local notation "b₂" => finiteNodeBoundaryEvaluation A hπ data D j
  (Nat.le_of_succ_le hj) hk0 hp Q w hw

include D hj hk0 hp hv hw

/-- Every later retained model distinguishes exactly the original divided residue coordinates. -/
theorem finitePointSpecialization_retained_eq_iff :
    finitePointSpecialization A hπ data (j + 1 + r) hr P =
      finitePointSpecialization A hπ data (j + 1 + r) hr Q ↔
        residue A v.a = residue A w.a ∧ residue A v.b = residue A w.b := by
  change finiteCoefficientPointSection A hπ data (j + 1 + r) hr F P =
    finiteCoefficientPointSection A hπ data (j + 1 + r) hr F Q ↔ _
  rw [← finiteCoefficientPointSection_retainedChart A hπ data j hj r hr F D hk0 hp P v hv,
    ← finiteCoefficientPointSection_retainedChart A hπ data j hj r hr F D hk0 hp Q w hw,
    cancel_mono]
  rw [WeierstrassDilatation.horizontalTensorPoint_eq_iff]
  change residue A (b₁ _) = residue A (b₂ _) ∧
    residue A (b₁ _) = residue A (b₂ _) ↔ _
  simp only [finiteNodeBoundaryEvaluation_base, finiteNodePointEvaluation,
    WeierstrassDilatation.evaluation_x, WeierstrassDilatation.evaluation_y]

/-- Retention at any two later stages creates no new identification of these original points. -/
theorem finitePointSpecialization_retained_eq_stable (t : ℕ) (ht : j + 1 + t ≤ n) :
    finitePointSpecialization A hπ data (j + 1 + r) hr P =
      finitePointSpecialization A hπ data (j + 1 + r) hr Q ↔
        finitePointSpecialization A hπ data (j + 1 + t) ht P =
          finitePointSpecialization A hπ data (j + 1 + t) ht Q := by
  rw [finitePointSpecialization_retained_eq_iff A hπ data D j hj r hr hk0 hp P Q v hv w hw,
    finitePointSpecialization_retained_eq_iff A hπ data D j hj t ht hk0 hp P Q v hv w hw]

end FLT.Mazur.WeierstrassDividedDepth
