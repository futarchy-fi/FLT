/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingChangeParameter
public import FLT.Mazur.NilpotentAlgebraAutomorphism

/-!
# Full node automorphisms from units congruent to one

Multiplying the two coordinates by inverse chart units preserves the smoothing
exactly. Congruence to one over a nilpotent coefficient ideal makes the resulting
endomorphism invertible by finite contraction, even when the unit is nonconstant.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)
local notation "A" => ChartRing t
local notation "x" => leftCoordinate t
local notation "y" => rightCoordinate t

/-- Balance a chart unit between the two coordinates of the original node. -/
def balancedUnitMap (v : Aˣ) : A →ₐ[R] A :=
  evaluate t (x * v) (y * ↑v⁻¹) (by
    rw [mul_mul_mul_comm, Units.mul_inv, mul_one, coordinate_relation])

/-- The entire left coordinate includes the prescribed chart unit. -/
@[simp] theorem balancedUnitMap_left (v : Aˣ) :
    balancedUnitMap t v x = x * v := evaluate_left ..

/-- The other coordinate compensates by the full inverse unit. -/
@[simp] theorem balancedUnitMap_right (v : Aˣ) :
    balancedUnitMap t v y = y * ↑v⁻¹ := evaluate_right ..

/-- The full node map is the identity modulo the original coefficient ideal. -/
theorem balancedUnitMap_sub_mem (I : Ideal R) (v : Aˣ)
    (hv : (v : A) - 1 ∈ I.map (algebraMap R A)) (z : A) :
    balancedUnitMap t v z - z ∈ I.map (algebraMap R A) := by
  let J := I.map (algebraMap R A)
  let q := Ideal.Quotient.mkₐ R J
  have hqv : q (v : A) = 1 := by
    exact (Ideal.Quotient.eq.mpr hv).trans (map_one q)
  have hqi : q (↑v⁻¹ : A) = 1 := by
    have h := congrArg q (Units.mul_inv v)
    rw [map_mul, map_one, hqv] at h
    exact (one_mul (q (↑v⁻¹ : A))).symm.trans h
  have hq : q.comp (balancedUnitMap t v) = q := by
    refine chartRing_hom_ext (S := A ⧸ J) t _ _ ?_ ?_
    · simp only [AlgHom.comp_apply, balancedUnitMap_left, map_mul, hqv]
      exact mul_one (q x)
    · simp only [AlgHom.comp_apply, balancedUnitMap_right, map_mul, hqi]
      exact mul_one (q y)
  exact Ideal.Quotient.eq.mp (DFunLike.congr_fun hq z)

/-- Nilpotence supplies the inverse on every chart function, not just on the punctures. -/
irreducible_def balancedUnitEquiv (I : Ideal R) (hI : IsNilpotent I) (v : Aˣ)
    (hv : (v : A) - 1 ∈ I.map (algebraMap R A)) : A ≃ₐ[R] A :=
  NilpotentAlgebraAutomorphism.equiv I (balancedUnitMap t v)
    (balancedUnitMap_sub_mem t I v hv) hI

/-- The inverse construction retains the prescribed forward homomorphism. -/
theorem balancedUnitEquiv_toAlgHom (I : Ideal R) (hI : IsNilpotent I) (v : Aˣ)
    (hv : (v : A) - 1 ∈ I.map (algebraMap R A)) :
    (balancedUnitEquiv t I hI v hv).toAlgHom = balancedUnitMap t v := by
  rw [balancedUnitEquiv_def, NilpotentAlgebraAutomorphism.equiv_toAlgHom]

/-- Every correction raises the original coefficient filtration by one. -/
theorem balancedUnitMap_error_mem_power (I : Ideal R) (v : Aˣ)
    (hv : (v : A) - 1 ∈ I.map (algebraMap R A)) (n : ℕ) (z : A)
    (hz : z ∈ (I.map (algebraMap R A)) ^ n) :
    balancedUnitMap t v z - z ∈ (I.map (algebraMap R A)) ^ (n + 1) :=
  NilpotentAlgebraAutomorphism.error_mem_power I (balancedUnitMap t v)
    (balancedUnitMap_sub_mem t I v hv) n z hz

end FLT.Mazur.PolygonSmoothing
