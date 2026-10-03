/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SplitKummerModel

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
variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Addition of geometric points has the split component/root formula. -/
theorem splitKummerCoordinates_add (x y : (splitKummerModel p n).Points) :
    (splitKummerCoordinates p n (x + y)).val =
      (KummerAlgebra.sumComponent (p ^ n) (pow_pos (Fact.out : p.Prime).pos _)
        (splitKummerCoordinates p n x).val.1 (splitKummerCoordinates p n y).val.1,
        (splitKummerCoordinates p n x).val.2 * (splitKummerCoordinates p n y).val.2) := by
  let hn := pow_pos (Fact.out : p.Prime).pos n
  let : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let e := KummerAlgebra.coordinateUnitPointsEquiv ℤ_[p] (p ^ n) 1 hn
    (S := AlgebraicClosure ℚ_[p])
  let r := Bialgebra.restrictPoints ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])
    (SplitKummerCoordinate p n)
  have h := KummerAlgebra.coordinateUnitPointsEquiv_convolution ℤ_[p] (p ^ n) 1 hn
    (e (r x)) (e (r y))
  simp only [e, Equiv.symm_apply_apply] at h
  have he := congrArg (fun f ↦ (e f).val) h
  simp only [e, Equiv.apply_symm_apply] at he
  change (e (r (x + y))).val =
    (KummerAlgebra.sumComponent (p ^ n) hn (e (r x)).val.1 (e (r y)).val.1,
      (e (r x)).val.2 * (e (r y)).val.2)
  rw [show r (x + y) = _ from Bialgebra.restrictPoints_mul
    ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]) (SplitKummerCoordinate p n) x y]
  change (e (KummerAlgebra.convolution ℤ_[p] (p ^ n) 1 hn
    (r x) (r y))).val = _
  simpa only [KummerAlgebra.mulUnitPoint, map_one, inv_one, one_pow, mul_one] using he

/-- Galois fixes the component and acts through its actual field action on the root. -/
theorem splitKummerCoordinates_smul (g : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
    (x : (splitKummerModel p n).Points) :
    (splitKummerCoordinates p n (g • x)).val =
      ((splitKummerCoordinates p n x).val.1,
        Units.map g.toRingEquiv.toMonoidHom (splitKummerCoordinates p n x).val.2) := by
  let hn := pow_pos (Fact.out : p.Prime).pos n
  let e := KummerAlgebra.coordinateUnitPointsEquiv ℤ_[p] (p ^ n) 1 hn
    (S := AlgebraicClosure ℚ_[p])
  let r := Bialgebra.restrictPoints ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])
    (SplitKummerCoordinate p n)
  let σ := g.toAlgHom.restrictScalars ℤ_[p]
  have h := KummerAlgebra.coordinateUnitPointsEquiv_comp ℤ_[p] (p ^ n) 1 hn σ
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
