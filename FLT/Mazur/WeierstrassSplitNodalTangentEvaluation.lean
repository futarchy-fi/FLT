/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalTangentLift

/-!
# Evaluating the actual addition map on all node tangent vectors

The secant specialization is constructed from the two input points. Its output
has reciprocal branch characters without any assumed factorization or output formula.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (a : R) (r q : Sˣ) (x y : S)
  (hq : (q : S) = (r : S) + algebraMap R S a)
  (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0)
local notation "W" => WeierstrassCurve.mk a 0 0 0 0
local notation "F" => splitNodalTangentLift a r q x y hq hxx hxy hyy
local notation "g" => additionChartAlgRestriction W (ordinaryIndex false)

/-- The constructed domain lift retains the full smooth input. -/
theorem splitNodalTangentLift_left (i : Fin 3) :
    F (g (productLeft W (coord W 2 i))) = ![(r : S) * q, (r : S) ^ 2 * q, 1] i := by
  have h := DFunLike.congr_fun
    (splitNodalTangentLift_restriction a r q x y hq hxx hxy hyy)
    (productLeft W (coord W 2 i))
  exact h.trans (splitNodalTangentPair_left a r q x y hq hxx hxy hyy i)

/-- The constructed domain lift retains the full infinitesimal node input. -/
theorem splitNodalTangentLift_right (i : Fin 3) :
    F (g (productRight W (coord W 2 i))) = ![x, y, 1] i := by
  have h := DFunLike.congr_fun
    (splitNodalTangentLift_restriction a r q x y hq hxx hxy hyy)
    (productRight W (coord W 2 i))
  exact h.trans (splitNodalTangentPair_right a r q x y hq hxx hxy hyy i)

/-- The output is the specialization of the original addition algebra map. -/
def splitNodalTangentOutput : Coordinate W 2 →ₐ[R] S :=
  (F).comp (ordinaryChartAddition W false)

/-- The actual output has the first branch character. -/
theorem splitNodalTangentOutput_first_character :
    (r : S) * splitNodalTangentOutput a r q x y hq hxx hxy hyy (coord W 2 1) =
      (q : S) * y := by
  have hleft := splitNodalTangentLift_left a r q x y hq hxx hxy hyy
  have hright := splitNodalTangentLift_right a r q x y hq hxx hxy hyy
  have hx : F (g (productX₂ W)) = x := hright 0
  have hy : F (g (productY₂ W)) = y := hright 1
  simpa only [splitNodalTangentOutput, AlgHom.comp_apply, hx, hy] using
    splitNodalTangentChart_first_character a r q false F hq
    (hleft 0) (hleft 1) (by rw [hx]; exact hxx) (by rw [hx, hy]; exact hxy)
    (by rw [hy]; exact hyy)

/-- The actual output has the opposite branch character. -/
theorem splitNodalTangentOutput_second_character :
    (q : S) * splitNodalTangentOutput a r q x y hq hxx hxy hyy
        (coord W 2 1 + algebraMap R _ a * coord W 2 0) =
      (r : S) * (y + algebraMap R S a * x) := by
  have hleft := splitNodalTangentLift_left a r q x y hq hxx hxy hyy
  have hright := splitNodalTangentLift_right a r q x y hq hxx hxy hyy
  have hx : F (g (productX₂ W)) = x := hright 0
  have hy : F (g (productY₂ W)) = y := hright 1
  simpa only [splitNodalTangentOutput, AlgHom.comp_apply, hx, hy] using
    splitNodalTangentChart_second_character a r q false F hq
    (hleft 0) (hleft 1) (by rw [hx]; exact hxx) (by rw [hx, hy]; exact hxy)
    (by rw [hy]; exact hyy)

/-- The first branch function scales by the Laurent ratio `q/r`. -/
theorem splitNodalTangentOutput_first_scaling :
    splitNodalTangentOutput a r q x y hq hxx hxy hyy (coord W 2 1) =
      (↑(q * r⁻¹) : S) * y := by
  apply r.isUnit.mul_right_inj.mp
  rw [splitNodalTangentOutput_first_character]
  simp only [Units.val_mul]
  calc
    (q : S) * y = ((r : S) * ↑r⁻¹) * ((q : S) * y) := by rw [Units.mul_inv, one_mul]
    _ = _ := by ring

/-- The opposite branch function scales by the inverse Laurent ratio. -/
theorem splitNodalTangentOutput_second_scaling :
    splitNodalTangentOutput a r q x y hq hxx hxy hyy
        (coord W 2 1 + algebraMap R _ a * coord W 2 0) =
      (↑(r * q⁻¹) : S) * (y + algebraMap R S a * x) := by
  apply q.isUnit.mul_right_inj.mp
  rw [splitNodalTangentOutput_second_character]
  simp only [Units.val_mul]
  calc
    (r : S) * (y + algebraMap R S a * x) =
        ((q : S) * ↑q⁻¹) * ((r : S) * (y + algebraMap R S a * x)) := by
      rw [Units.mul_inv, one_mul]
    _ = _ := by ring

end FLT.Mazur.WeierstrassIntegralChart
