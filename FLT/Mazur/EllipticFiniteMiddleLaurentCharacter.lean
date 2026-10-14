/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteMiddleSpecialization
public import FLT.Mazur.WeierstrassDilatationTerminalSectionBranches
public import FLT.Mazur.LaurentUnitPoints

/-!
# The original character of an even-middle specialization

The actual terminal Laurent point has the primitive vertical residue as its
unit parameter. This identifies the entire proper specialization on the
middle component, where the two arithmetic signs coincide.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j) ≤ depth)
  (hm : 2 * (start + j) = depth)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
local notation "F" => ResidueField A
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "ev" => finiteNodePointEvaluation A hπ data j hj P v hv
local notation "f" => WeierstrassDilatation.sectionResidueEvaluation
  (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) ev
local notation "e" => WeierstrassDilatation.residueLaurentEquiv D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hm
local notation "g" => WeierstrassDilatation.normalizedSectionEvaluation f e

/-- The original terminal Laurent character is a unit, constructed from the actual tensor point. -/
def finiteMiddleLaurentUnit : Fˣ := LaurentUnitPoints.pointUnit g

/-- The middle character is exactly the original primitive vertical residue. -/
theorem finiteMiddleLaurentUnit_val :
    (finiteMiddleLaurentUnit A hπ data D j hj hk0 hk hm P v hv : F) = residue A v.b := by
  change g (LaurentPolynomial.T 1) = _
  have h := WeierstrassDilatation.normalizedSectionEvaluation_apply f e
    (WeierstrassDilatation.tensorY W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d) F)
  rw [WeierstrassDilatation.residueLaurentEquiv_y,
    WeierstrassDilatation.sectionResidueEvaluation_y] at h
  change g (LaurentPolynomial.T 1) = residue A
    (WeierstrassDilatation.evaluation W _ _ _ _ v.a v.b _ _) at h
  rw [WeierstrassDilatation.evaluation_y] at h
  exact h

/-- The actual middle Laurent point is evaluation at that original unit. -/
theorem finiteMiddleLaurentPoint_eq_unit :
    finiteMiddleLaurentPoint A hπ data D j hj hk0 hk hm P v hv =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F)
        (finiteMiddleLaurentUnit A hπ data D j hj hk0 hk hm P v hv)).toRingHom) := by
  rw [finiteMiddleLaurentUnit, LaurentUnitPoints.evalUnit_pointUnit]
  rw [WeierstrassDilatation.normalizedSectionEvaluation_def]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The even-middle proper specialization retains exactly its original Laurent parameter. -/
theorem finitePointSpecialization_middle_character :
    finitePointSpecialization A hπ data j hj P =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F)
        (finiteMiddleLaurentUnit A hπ data D j hj hk0 hk hm P v hv)).toRingHom) ≫
          terminalLaurentChart hπ data D j hj hk0 hk hm := by
  rw [← finiteMiddleLaurentPoint_inclusion A hπ data D j hj hk0 hk hm P v hv,
    finiteMiddleLaurentPoint_eq_unit]

end FLT.Mazur.WeierstrassDividedDepth
