/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteNodeLaurentSpecialization

/-!
# Original Laurent equality at a terminal node chart

The actual terminal node chart and each punctured branch are open immersions.
Consequently equality of original proper specializations detects exactly the
original Laurent residue, including at the final odd depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Spectrum evaluation at a Laurent unit remembers the original unit. -/
theorem laurentUnitSpec_eq_iff {F : Type u} [Field F] (a b : Fˣ) :
    Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F) a).toRingHom) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F) b).toRingHom) ↔
        a = b := by
  constructor
  · intro h
    have he : LaurentUnitPoints.evalUnit (R := F) a = LaurentUnitPoints.evalUnit b :=
      AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h))
    simpa only [LaurentUnitPoints.pointUnit_evalUnit] using
      congrArg LaurentUnitPoints.pointUnit he
  · rintro rfl
    rfl

variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
  (P Q : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
  (w : NodePointCoordinates A W π Q) (hw : w.depth = start + j)

include D hk0 hp hv hw

/-- At the original node stage, a negative-branch residue detects specialization equality. -/
theorem finitePointSpecialization_terminal_negative_eq_iff
    (hb : IsUnit v.b) (hd : IsUnit w.b) :
    finitePointSpecialization A hπ data j hj P =
      finitePointSpecialization A hπ data j hj Q ↔ residue A v.b = residue A w.b := by
  rw [finitePointSpecialization_negative_laurent A hπ data D j hj hk0 (by omega) hp P v hv hb,
    finitePointSpecialization_negative_laurent A hπ data D j hj hk0 (by omega) hp Q w hw hd,
    ← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono, laurentUnitSpec_eq_iff,
    ← Units.val_inj, nodeNegativeLaurentUnit_val, nodeNegativeLaurentUnit_val]

/-- At the original node stage, the positive tangent residue detects specialization equality. -/
theorem finitePointSpecialization_terminal_positive_eq_iff
    (hb : IsUnit (v.b + W.a₁ * v.a)) (hd : IsUnit (w.b + W.a₁ * w.a)) :
    finitePointSpecialization A hπ data j hj P =
      finitePointSpecialization A hπ data j hj Q ↔
        residue A (v.b + W.a₁ * v.a) = residue A (w.b + W.a₁ * w.a) := by
  rw [finitePointSpecialization_positive_laurent A hπ data D j hj hk0 (by omega) hp P v hv hb,
    finitePointSpecialization_positive_laurent A hπ data D j hj hk0 (by omega) hp Q w hw hd,
    ← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono, laurentUnitSpec_eq_iff,
    ← Units.val_inj, nodePositiveLaurentUnit_val, nodePositiveLaurentUnit_val]

end FLT.Mazur.WeierstrassDividedDepth
