/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialFormulaCoordinates
public import FLT.Mazur.WeierstrassModificationXUnitIncidence

/-!
# The entire initial chart has punctured depth-zero formula coordinates

At creation depth zero the scale is one. The recovered horizontal coordinate
is therefore a unit on the entire initial chart, before any smooth restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R}
  (d : Data W π 0)
local notation "x" => WeierstrassDilatation.x W (π ^ 0) d.b3 d.b4 d.b6
local notation "u" => WeierstrassModificationX.x W (π ^ 0) d.b3 d.b4 d.b6
local notation "B" => WeierstrassModificationX.Coordinate W (π ^ 0) d.b3 d.b4 d.b6

/-- At scale one, recovering divided coordinates preserves the actual horizontal coordinate. -/
theorem initialFormulaCoordinateHom_x : initialFormulaCoordinateHom d x = u := by
  have h := congrArg (fun f => f (WeierstrassIntegralChart.coord W 2 0))
    (initialFormulaCoordinateHom_original d)
  simpa only [AlgHom.comp_apply, WeierstrassDilatation.fromOriginal_x,
    pow_zero, map_one, one_mul, WeierstrassModificationX.fromOriginal_x] using h

/-- Every original initial prime has nonzero divided horizontal coordinate. -/
theorem initialFormulaCoordinates_punctured (p : Spec (.of B)) :
    x ∉ (initialFormulaCoordinates d p).asIdeal := by
  change initialFormulaCoordinateHom d x ∉ p.asIdeal
  rw [initialFormulaCoordinateHom_x]
  intro hp
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp
    (WeierstrassModificationX.x_isUnit_of_scale_isUnit W (π ^ 0) d.b3 d.b4 d.b6
      (by simpa only [pow_zero] using (isUnit_one : IsUnit (1 : R)))))

variable {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d₀" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "idx" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))

/-- Retention at any final stage preserves the unconditional initial horizontal puncture. -/
theorem retainedInitialFormulaCoordinates_punctured
    (p : globalIntegralAtlasObject data j hj idx) :
    WeierstrassDilatation.x W (π ^ 0) (d₀).b3 (d₀).b4 (d₀).b6 ∉
      (retainedInitialFormulaCoordinates data j hj p).asIdeal :=
  initialFormulaCoordinates_punctured d₀ ((eqToHom (finiteInitialExteriorObject_eq data j hj)) p)

end FLT.Mazur.WeierstrassDividedDepth
