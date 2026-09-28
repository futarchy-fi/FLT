/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD
public import FLT.GaloisRepresentation.HardlyRamified.KummerTwoField
public import FLT.GroupScheme.HopfPoints
public import FLT.GroupScheme.KummerTwist

/-!
# The Kummer object attached to two

The coordinate Hopf algebra has three components, with equations `X³ = 2ⁱ`.
It is finite free over `ℤ[1/2]`; the carry multiplication on components
defines its group law even at the prime three.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped TensorProduct

namespace ThreeAdicPlan

/-- Two as a unit of the coefficient ring `ℤ[1/2]`. -/
def kummerTwoUnit : ZInvTwoˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := ZInvTwo) (2 : ℤ)).unit

/-- The unit parameter of the Kummer model is the integer two. -/
@[simp] theorem kummerTwoUnit_val : (kummerTwoUnit : ZInvTwo) = 2 := by
  simp [kummerTwoUnit]

/-- The actual coordinate algebra of the three-torsion Kummer extension for two. -/
abbrev KummerTwoCoordinate := KummerAlgebra.Coordinate ZInvTwo 3 kummerTwoUnit

instance : HopfAlgebra.IsFiniteFlat ZInvTwo KummerTwoCoordinate :=
  KummerAlgebra.coordinate_isFiniteFlat ZInvTwo 3 kummerTwoUnit (by decide)

instance : Algebra.Etale ℚ (ℚ ⊗[ZInvTwo] KummerTwoCoordinate) :=
  KummerAlgebra.generic_etale ZInvTwo 3 kummerTwoUnit (by decide) (by norm_num)

instance : CommGroup (ℚ ⊗[ZInvTwo] KummerTwoCoordinate →ₐ[ℚ] AlgebraicClosure ℚ) :=
  HopfAlgebra.pointsCommGroup ℚ (AlgebraicClosure ℚ) _

/-- The full continuous Galois module of the geometric points of the Kummer Hopf algebra. -/
abbrev kummerTwoPoints : FiniteContinuousGaloisModule where
  Carrier := Additive (ℚ ⊗[ZInvTwo] KummerTwoCoordinate →ₐ[ℚ] AlgebraicClosure ℚ)

/-- The explicit finite-flat model, with its identity generic point comparison. -/
def kummerTwoModel : ModelOverZInvTwo kummerTwoPoints where
  CoordinateRing := KummerTwoCoordinate
  points :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  points_bijective := Function.bijective_id

/-- The finite-flat Kummer object attached to the unit two and killed by three. -/
def kummerTwoObject : FiniteFlatObject ZInvTwo := FiniteFlatObject.ofModel kummerTwoModel

/-- Restriction identifies generic points with points of the integral coordinate algebra. -/
def kummerTwoPointEquiv : kummerTwoPoints ≃ (KummerTwoCoordinate →ₐ[ZInvTwo]
    AlgebraicClosure ℚ) :=
  (Equiv.refl _).trans (Bialgebra.restrictPoints ZInvTwo ℚ (AlgebraicClosure ℚ) _)

/-- A root of `X³ = 2ⁱ` gives a geometric point in component `i`. -/
def kummerTwoRootPoint (i : Fin 3) (x : AlgebraicClosure ℚ)
    (hx : x ^ 3 = 2 ^ i.val) : kummerTwoPoints :=
  kummerTwoPointEquiv.symm (KummerAlgebra.rootPoint ZInvTwo 3 kummerTwoUnit i x
    (by simpa [map_ofNat] using hx))

/-- Restriction of a root point recovers its integral coordinates. -/
@[simp] theorem kummerTwoPointEquiv_rootPoint (i : Fin 3) (x : AlgebraicClosure ℚ)
    (hx : x ^ 3 = 2 ^ i.val) :
    kummerTwoPointEquiv (kummerTwoRootPoint i x hx) =
      KummerAlgebra.rootPoint ZInvTwo 3 kummerTwoUnit i x (by simpa [map_ofNat] using hx) :=
  kummerTwoPointEquiv.apply_symm_apply _

/-- Every geometric point has root coordinates in one of the three components. -/
theorem kummerTwoRootPoint_surjective (P : kummerTwoPoints) :
    ∃ (i : Fin 3) (x : AlgebraicClosure ℚ) (hx : x ^ 3 = 2 ^ i.val),
      kummerTwoRootPoint i x hx = P := by
  let e := KummerAlgebra.coordinatePointsEquiv ZInvTwo 3 kummerTwoUnit
    (S := AlgebraicClosure ℚ)
  obtain ⟨⟨i, x, hx⟩, h⟩ := e.symm.surjective (kummerTwoPointEquiv P)
  refine ⟨i, x, by simpa [map_ofNat] using hx, ?_⟩
  apply kummerTwoPointEquiv.injective
  rw [kummerTwoPointEquiv_rootPoint]
  exact h

/-- Equal root coordinates define the same geometric point. -/
theorem kummerTwoRootPoint_congr {i j : Fin 3} {x y : AlgebraicClosure ℚ}
    {hx : x ^ 3 = 2 ^ i.val} {hy : y ^ 3 = 2 ^ j.val} (hi : i = j) (hxy : x = y) :
    kummerTwoRootPoint i x hx = kummerTwoRootPoint j y hy := by
  subst j
  subst y
  rfl

/-- The carry expression is again a root in the sum component. -/
theorem kummerTwoRootPoint_add_root (i j : Fin 3) (x y : AlgebraicClosure ℚ)
    (hx : x ^ 3 = 2 ^ i.val) (hy : y ^ 3 = 2 ^ j.val) :
    (x * y * (2 : AlgebraicClosure ℚ)⁻¹ ^ ((i.val + j.val) / 3)) ^ 3 =
      2 ^ (KummerAlgebra.sumComponent 3 (by decide) i j).val := by
  have h := KummerAlgebra.mul_carry_pow ZInvTwo 3 kummerTwoUnit
    (show x ^ 3 = algebraMap ZInvTwo (AlgebraicClosure ℚ)
      ((kummerTwoUnit : ZInvTwo) ^ i.val) by simpa [map_ofNat] using hx)
    (show y ^ 3 = algebraMap ZInvTwo (AlgebraicClosure ℚ)
      ((kummerTwoUnit : ZInvTwo) ^ j.val) by simpa [map_ofNat] using hy)
    (Nat.mod_add_div (i.val + j.val) 3).symm
  simpa [KummerAlgebra.sumComponent, ← map_inv, map_ofNat] using h

/-- Addition of geometric points is the explicit Kummer carry law. -/
theorem kummerTwoRootPoint_add (i j : Fin 3) (x y : AlgebraicClosure ℚ)
    (hx : x ^ 3 = 2 ^ i.val) (hy : y ^ 3 = 2 ^ j.val) :
    kummerTwoRootPoint i x hx + kummerTwoRootPoint j y hy =
      kummerTwoRootPoint (KummerAlgebra.sumComponent 3 (by decide) i j)
        (x * y * (2 : AlgebraicClosure ℚ)⁻¹ ^ ((i.val + j.val) / 3))
        (kummerTwoRootPoint_add_root i j x y hx hy) := by
  apply kummerTwoPointEquiv.injective
  change Bialgebra.restrictPoints ZInvTwo ℚ (AlgebraicClosure ℚ) _
      ((Additive.toMul (kummerTwoRootPoint i x hx) :
        ℚ ⊗[ZInvTwo] KummerTwoCoordinate →ₐ[ℚ] AlgebraicClosure ℚ) *
        (Additive.toMul (kummerTwoRootPoint j y hy) :
          ℚ ⊗[ZInvTwo] KummerTwoCoordinate →ₐ[ℚ] AlgebraicClosure ℚ)) = _
  rw [Bialgebra.restrictPoints_mul]
  change KummerAlgebra.convolution ZInvTwo 3 kummerTwoUnit (by decide)
    (kummerTwoPointEquiv (kummerTwoRootPoint i x hx))
    (kummerTwoPointEquiv (kummerTwoRootPoint j y hy)) = _
  simp only [kummerTwoRootPoint, Equiv.apply_symm_apply,
    KummerAlgebra.convolution_rootPoint]
  apply KummerAlgebra.rootPoint_congr _ _ _ rfl
  simp [map_ofNat]

/-- Component zero with root one is the identity point. -/
theorem kummerTwoRootPoint_zero : kummerTwoRootPoint 0 1 (by simp) = 0 := by
  apply kummerTwoPointEquiv.injective
  rw [kummerTwoPointEquiv_rootPoint]
  refine (KummerAlgebra.ofId_comp_counit ZInvTwo 3 kummerTwoUnit (by decide)
    (S := AlgebraicClosure ℚ)).symm.trans ?_
  ext a
  change algebraMap ZInvTwo (AlgebraicClosure ℚ) (Coalgebra.counit a) =
    algebraMap ℚ (AlgebraicClosure ℚ)
      (Coalgebra.counit (1 ⊗ₜ[ZInvTwo] a : ℚ ⊗[ZInvTwo] KummerTwoCoordinate))
  simp only [TensorProduct.counit_tmul, Bialgebra.counit_one, Algebra.smul_def, mul_one]
  exact IsScalarTower.algebraMap_apply ZInvTwo ℚ (AlgebraicClosure ℚ) _

/-- The Kummer point group is annihilated by three. -/
theorem kummerTwoObject_killedBy_three : KilledBy 3 kummerTwoObject := by
  change ∀ P : kummerTwoPoints, (3 : ℕ) • P = 0
  intro P
  obtain ⟨i, x, hx, rfl⟩ := kummerTwoRootPoint_surjective P
  rw [show (3 : ℕ) • kummerTwoRootPoint i x hx =
    (kummerTwoRootPoint i x hx + kummerTwoRootPoint i x hx) +
      kummerTwoRootPoint i x hx by simp [succ_nsmul, add_assoc]]
  rw [kummerTwoRootPoint_add, kummerTwoRootPoint_add, ← kummerTwoRootPoint_zero]
  apply kummerTwoRootPoint_congr
  · fin_cases i <;> decide
  · fin_cases i <;> norm_num [KummerAlgebra.sumComponent] at hx ⊢ <;>
      ring_nf <;> simp [hx]

/-- The Kummer point group has order nine. -/
theorem kummerTwoPoints_card : Nat.card kummerTwoPoints = 9 := by
  change Nat.card (ℚ ⊗[ZInvTwo] KummerTwoCoordinate →ₐ[ℚ] AlgebraicClosure ℚ) = 9
  rw [← GaloisModule.finrank_eq_natCard_algHom]
  rw [(KummerAlgebra.coordinateBaseChange ZInvTwo 3 kummerTwoUnit
    (S := ℚ)).toLinearEquiv.finrank_eq]
  let u := Units.map (algebraMap ZInvTwo ℚ).toMonoidHom kummerTwoUnit
  let (i : Fin 3) := KummerAlgebra.component_finite ℚ 3 u (by decide) i
  change Module.finrank ℚ ((i : Fin 3) → KummerAlgebra.Component ℚ 3 u i) = 9
  rw [Module.finrank_pi_fintype]
  have h (i : Fin 3) : Module.finrank ℚ (KummerAlgebra.Component ℚ 3 u i) = 3 := by
    change Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {KummerAlgebra.equation ℚ 3 u i}) = 3
    rw [finrank_quotient_span_eq_natDegree]
    rw [KummerAlgebra.equation, Polynomial.natDegree_X_pow_sub_C]
  simp [h]

end ThreeAdicPlan
