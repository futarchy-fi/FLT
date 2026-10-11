/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryConormalError
public import FLT.Mazur.WeierstrassOrdinaryCenterIdeal

/-!
# Integral branch characters modulo the residue conormal relations

The relevant relations are `I² + J*I`, where `I` is the center and `J` is the
base residue ideal. Keeping `J*I` retains the base generator at arbitrary depth.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (b : Bool)
  (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S) (I J : Ideal S)
local notation "a" => algebraMap R S W.a₁
local notation "x" => f (ordinaryInputRight W b (coord W 2 0))
local notation "y" => f (ordinaryInputRight W b (coord W 2 1))
local notation "X" => f (ordinaryChartAddition W b (coord W 2 0))
local notation "Y" => f (ordinaryChartAddition W b (coord W 2 1))
local notation "l" => f (ordinaryChartSlope W b)

/-- The exact first error lies in the residue conormal relations. -/
theorem ordinarySpecialization_first_conormal
    (h2 : algebraMap R S W.a₂ ∈ J) (h3 : algebraMap R S W.a₃ ∈ I)
    (h4 : algebraMap R S W.a₄ ∈ J * I) (hx : x ∈ I) (hy : y ∈ I) :
    l * Y - (l + a) * y ∈ I ^ 2 + J * I := by
  have hX := (ordinarySpecialization_output_mem_center W b f I h3
    (Ideal.mul_le_right h4) hx hy).1
  have hquad : X ^ 2 + x * X + x ^ 2 ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.add_mem _ (Ideal.add_mem _
      (by simpa only [pow_two] using Ideal.mul_mem_mul hX hX)
      (Ideal.mul_mem_mul hx hX))
      (by simpa only [pow_two] using Ideal.mul_mem_mul hx hx)
  have hleft : I ^ 2 ≤ I ^ 2 + J * I := le_sup_left
  have hright : J * I ≤ I ^ 2 + J * I := le_sup_right
  rw [ordinarySpecialization_first_error]
  exact (I ^ 2 + J * I).neg_mem (Ideal.add_mem _
    (Ideal.add_mem _ (hleft hquad)
      (hright (Ideal.mul_mem_mul h2 (I.add_mem hX hx)))) (hright h4))

/-- The opposite error also vanishes, with the divided third coefficient accounted for. -/
theorem ordinarySpecialization_second_conormal
    (h2 : algebraMap R S W.a₂ ∈ J) (h3 : algebraMap R S W.a₃ ∈ J * I)
    (h4 : algebraMap R S W.a₄ ∈ J * I) (hx : x ∈ I) (hy : y ∈ I) :
    (l + a) * (Y + a * X) - l * (y + a * x) ∈ I ^ 2 + J * I := by
  have h := ordinarySpecialization_first_conormal W b f I J h2
    (Ideal.mul_le_right h3) h4 hx hy
  rw [ordinarySpecialization_first_error] at h
  have hright : J * I ≤ I ^ 2 + J * I := le_sup_right
  rw [ordinarySpecialization_second_error, neg_add_rev]
  exact Ideal.add_mem _
    ((I ^ 2 + J * I).neg_mem (hright ((J * I).mul_mem_left a h3))) h

end FLT.Mazur.WeierstrassIntegralChart
