/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SplitKummerGeneralModel

/-! # Addition and Galois action on the split Kummer model

The component adds modulo the level and the root multiplies. Galois fixes
that component and acts on the root. The comparison of the root action with
cyclotomic scalars on the standard tensor quotient is a separate step.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ThreeAdicPlan
open scoped TensorProduct
variable (R K : Type) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Addition of geometric points has the split component/root formula. -/
theorem generalSplitKummerCoordinates_add (x y : (generalSplitKummerModel R K p n).Points) :
    (generalSplitKummerCoordinates R K p n (x + y)).val =
      (KummerAlgebra.sumComponent (p ^ n) (pow_pos (Fact.out : p.Prime).pos _)
        (generalSplitKummerCoordinates R K p n x).val.1
        (generalSplitKummerCoordinates R K p n y).val.1,
        (generalSplitKummerCoordinates R K p n x).val.2 *
          (generalSplitKummerCoordinates R K p n y).val.2) := by
  let hn := pow_pos (Fact.out : p.Prime).pos n
  let : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let e := KummerAlgebra.coordinateUnitPointsEquiv R (p ^ n) 1 hn
    (S := AlgebraicClosure K)
  let r := Bialgebra.restrictPoints R K (AlgebraicClosure K)
    (GeneralSplitKummerCoordinate R p n)
  have h := KummerAlgebra.coordinateUnitPointsEquiv_convolution R (p ^ n) 1 hn
    (e (r x)) (e (r y))
  simp only [e, Equiv.symm_apply_apply] at h
  have he := congrArg (fun f ↦ (e f).val) h
  simp only [e, Equiv.apply_symm_apply] at he
  change (e (r (x + y))).val =
    (KummerAlgebra.sumComponent (p ^ n) hn (e (r x)).val.1 (e (r y)).val.1,
      (e (r x)).val.2 * (e (r y)).val.2)
  rw [show r (x + y) = _ from Bialgebra.restrictPoints_mul
    R K (AlgebraicClosure K) (GeneralSplitKummerCoordinate R p n) x y]
  change (e (KummerAlgebra.convolution R (p ^ n) 1 hn
    (r x) (r y))).val = _
  simpa only [KummerAlgebra.mulUnitPoint, map_one, inv_one, one_pow, mul_one] using he

/-- Galois fixes the component and acts through its actual field action on the root. -/
theorem generalSplitKummerCoordinates_smul (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : (generalSplitKummerModel R K p n).Points) :
    (generalSplitKummerCoordinates R K p n (g • x)).val =
      ((generalSplitKummerCoordinates R K p n x).val.1,
        Units.map g.toRingEquiv.toMonoidHom (generalSplitKummerCoordinates R K p n x).val.2) := by
  let hn := pow_pos (Fact.out : p.Prime).pos n
  let e := KummerAlgebra.coordinateUnitPointsEquiv R (p ^ n) 1 hn
    (S := AlgebraicClosure K)
  let r := Bialgebra.restrictPoints R K (AlgebraicClosure K)
    (GeneralSplitKummerCoordinate R p n)
  let σ := g.toAlgHom.restrictScalars R
  have h := KummerAlgebra.coordinateUnitPointsEquiv_comp R (p ^ n) 1 hn σ
    (e (r x))
  simp only [e, Equiv.symm_apply_apply] at h
  have he := congrArg (fun f ↦ (e f).val) h
  simp only [e, Equiv.apply_symm_apply] at he
  change (e (r (g • x))).val = _
  have hr : r (g • x) = σ.comp (r x) := by
    ext a
    rfl
  rw [hr]
  exact he

end ThreeAdicPlan
