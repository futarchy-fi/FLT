/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudNakayamaDescent

/-!
# Jacobson augmentation for connected order-three quotients

In Oort--Tate coordinates, a nonunit cubic coefficient makes the augmentation
ideal Jacobson. This supplies the arithmetic hypothesis in Nakayama descent.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan.OortTateThreeBasis

variable {A : Type} [CommRing A] [HopfAlgebra ℤ_[3] A]

/-- The odd coordinate has zero augmentation. -/
theorem counit_x (P : OortTateThreeBasis ℤ_[3] A) :
    Coalgebra.counit (R := ℤ_[3]) P.x = 0 := by
  have h := HopfAlgebra.counit_antipode (R := ℤ_[3]) P.x
  rw [P.antipode, map_neg] at h
  have hz : (2 : ℤ_[3]) * Coalgebra.counit (R := ℤ_[3]) P.x = 0 := by
    linear_combination -h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The augmentation of an element is its constant Oort--Tate coefficient. -/
theorem counit_eq_repr_zero (P : OortTateThreeBasis ℤ_[3] A) (z : A) :
    Coalgebra.counit (R := ℤ_[3]) z = P.basis.repr z 0 := by
  let ε := Bialgebra.counitAlgHom ℤ_[3] A
  have hx : ε P.x = 0 := P.counit_x
  have h := congrArg ε (P.expansion z)
  change ε z = P.basis.repr z 0
  simpa only [map_add, map_smul, map_one, map_pow, hx, zero_pow (by decide : 2 ≠ 0),
    smul_zero, add_zero, smul_eq_mul, mul_one, mul_zero] using h

/-- A nonunit cubic coefficient places the odd coordinate in every maximal ideal. -/
theorem x_mem_jacobson_of_not_isUnit [Module.Finite ℤ_[3] A]
    (P : OortTateThreeBasis ℤ_[3] A) (ha : ¬ IsUnit P.a) :
    P.x ∈ (⊥ : Ideal A).jacobson := by
  apply Submodule.mem_sInf.mpr
  intro m hm
  let : Ideal.IsMaximal m := hm.2
  have hmR := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[3]) m
  have haR : P.a ∈ Ideal.under ℤ_[3] m := by
    rw [IsLocalRing.eq_maximalIdeal hmR]
    exact ha
  have hp : P.x ^ 3 ∈ m := by
    rw [P.cube, Algebra.smul_def]
    exact Ideal.mul_mem_right P.x m haR
  exact Ideal.IsPrime.mem_of_pow_mem (inferInstance : Ideal.IsPrime m) 3 hp

/-- The augmentation ideal of a ramified order-three presentation is Jacobson. -/
theorem counit_ker_le_jacobson_of_not_isUnit [Module.Finite ℤ_[3] A]
    (P : OortTateThreeBasis ℤ_[3] A) (ha : ¬ IsUnit P.a) :
    RingHom.ker (Bialgebra.counitAlgHom ℤ_[3] A).toRingHom ≤ (⊥ : Ideal A).jacobson := by
  intro z hz
  have hz0 : P.basis.repr z 0 = 0 := (P.counit_eq_repr_zero z).symm.trans hz
  rw [P.expansion z, hz0, zero_smul, zero_add]
  apply Ideal.add_mem
  · exact Submodule.smul_mem (((⊥ : Ideal A).jacobson).restrictScalars ℤ_[3]) _
      (P.x_mem_jacobson_of_not_isUnit ha)
  · exact Submodule.smul_mem (((⊥ : Ideal A).jacobson).restrictScalars ℤ_[3]) _
      (Ideal.pow_mem_of_mem _ (P.x_mem_jacobson_of_not_isUnit ha) 2 (by decide))

end ThreeAdicPlan.OortTateThreeBasis

namespace ThreeAdicPlan

/-- For a ramified order-three quotient presentation, relative flatness is the
remaining hypothesis needed by the order-three middle-map descent argument. -/
theorem GenericGaloisHom.middle_surjective_of_order_three_layers_of_nonunit
    {S X X' Y Y' : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X)
    (q : GenericGaloisHom X Y) (q' : GenericGaloisHom X' Y')
    (hi : Function.Injective i) (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x) (hS : Nat.card S.Points = 3)
    (g : ModelHom X X') (hj : Function.Injective ((genericHom g).comp i))
    (h : GenericGaloisHom Y Y') (hc : q'.comp (genericHom g) = h.comp q)
    (hh : Function.Surjective h) (hY : Nat.card Y.Points = 3) (hY' : Nat.card Y'.Points = 3)
    [Module.Flat q.quotientCoordinates X.CoordinateRing]
    (P : OortTateThreeBasis ℤ_[3] q.quotientCoordinates) (ha : ¬ IsUnit P.a) :
    Function.Surjective g :=
  i.middle_surjective_of_order_three_layers_of_le_jacobson q q' hi hq hq' hexact hS
    g hj h hc hh hY hY' (P.counit_ker_le_jacobson_of_not_isUnit ha)

end ThreeAdicPlan
