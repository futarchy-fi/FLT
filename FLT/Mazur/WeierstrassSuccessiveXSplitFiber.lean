/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMonicComparison
public import FLT.Mazur.WeierstrassModificationXFiberIntersectionSplit

/-!
# Two ordered incidence nodes in the successive fiber before the middle depth

When the divided coefficients vanish, the slope has the separated roots
0 and -a₁. Chinese remainders identify the actual three-generator chart with
two copies of R[t,u]/(tu), retaining both coordinates and their orientation.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "B" => SuccessiveIncidence.Coordinate (0 : R)

include h2 in
/-- The specialized slope polynomial has its two actual ordered linear factors. -/
theorem split_slopePolynomial :
    slopePolynomial W 0 0 0 0 0 = (X * (X + C (algebraMap R B W.a₁)) : B[X]) := by
  simp only [slopePolynomial, h2, map_zero, zero_mul, add_zero, sub_zero]
  ring

/-- Split the actual monic fiber into its two ordered incidence components. -/
def splitMonicEquiv : MonicCoordinate W 0 0 0 0 0 ≃ₐ[B] B × B :=
  (AdjoinRoot.algEquivOfEq B _ _ (split_slopePolynomial W h2)).trans
    (WeierstrassModificationX.intersectionSplitEquiv (algebraMap R B W.a₁)
      (ha.map (algebraMap R B)))

/-- The original slope takes the ordered values zero and minus the original tangent unit. -/
@[simp] theorem splitMonicEquiv_v :
    splitMonicEquiv W h2 ha (monicV W 0 0 0 0 0) = (0, -algebraMap R B W.a₁) := by
  change WeierstrassModificationX.intersectionSplitEquiv _ (ha.map (algebraMap R B))
    ((AdjoinRoot.algEquivOfEq B _ _ (split_slopePolynomial W h2)) (AdjoinRoot.root _)) = _
  rw [AdjoinRoot.algEquivOfEq_root]
  change WeierstrassModificationX.intersectionSplitRingEquiv
    (algebraMap R B W.a₁) (ha.map (algebraMap R B)) (Ideal.Quotient.mk _ X) = _
  apply Prod.ext
  · simpa only [eval_X] using WeierstrassModificationX.intersectionSplitRingEquiv_fst
      (algebraMap R B W.a₁) (ha.map (algebraMap R B)) X
  · simpa only [eval_X] using WeierstrassModificationX.intersectionSplitRingEquiv_snd
      (algebraMap R B W.a₁) (ha.map (algebraMap R B)) X

/-- The entire three-generator zero-coefficient fiber is an ordered pair of incidence nodes. -/
def splitFiberEquiv : Coordinate W 0 0 0 0 0 ≃ₐ[R] B × B :=
  (monicEquiv W 0 0 0 0 0).trans ((splitMonicEquiv W h2 ha).restrictScalars R)

/-- Both components retain the original incidence ratio. -/
@[simp] theorem splitFiberEquiv_t :
    splitFiberEquiv W h2 ha (coord W 0 0 0 0 0 0) =
      (SuccessiveIncidence.t (0 : R), SuccessiveIncidence.t (0 : R)) := by
  change splitMonicEquiv W h2 ha (toMonic W 0 0 0 0 0 (coord W 0 0 0 0 0 0)) = _
  rw [toMonic_coord]
  exact (splitMonicEquiv W h2 ha).commutes (SuccessiveIncidence.t (0 : R))

/-- The two components keep the original separated tangent slopes. -/
@[simp] theorem splitFiberEquiv_v :
    splitFiberEquiv W h2 ha (coord W 0 0 0 0 0 1) = (0, -algebraMap R B W.a₁) := by
  change splitMonicEquiv W h2 ha (toMonic W 0 0 0 0 0 (coord W 0 0 0 0 0 1)) = _
  rw [toMonic_coord]
  exact splitMonicEquiv_v W h2 ha

/-- Both components retain the original horizontal coordinate, including at their nodes. -/
@[simp] theorem splitFiberEquiv_u :
    splitFiberEquiv W h2 ha (coord W 0 0 0 0 0 2) =
      (SuccessiveIncidence.u (0 : R), SuccessiveIncidence.u (0 : R)) := by
  change splitMonicEquiv W h2 ha (toMonic W 0 0 0 0 0 (coord W 0 0 0 0 0 2)) = _
  rw [toMonic_coord]
  exact (splitMonicEquiv W h2 ha).commutes (SuccessiveIncidence.u (0 : R))

end FLT.Mazur.WeierstrassSuccessiveX
