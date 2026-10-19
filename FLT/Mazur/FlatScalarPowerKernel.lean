/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarKernelExtension
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Flat transport of scalar equations at a fixed power

Flatness preserves the exact scalar annihilator of each test power. Thus a
branch equation outside a branch prime gives an original scalar equation
with the SAME exponent, rather than only a later vanishing power.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatScalarPowerKernel
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- Original scalars killing a specified power of a coefficient. -/
def powerKernel (b : B) (k : ℕ) : Ideal R :=
  LinearMap.ker (LinearMap.toSpanSingleton R B (b ^ k))

/-- Membership is an exact equation in the full original ring. -/
theorem mem_powerKernel (b : B) (k : ℕ) (r : R) :
    r ∈ powerKernel (R := R) b k ↔ b ^ k * algebraMap R B r = 0 := by
  change r • b ^ k = 0 ↔ _
  rw [Algebra.smul_def, mul_comm]

variable (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]
local notation "B'" => S ⊗[R] B
local notation "j" => Algebra.TensorProduct.includeRight (R := R) (A := S) (B := B)

/-- Flat extension preserves scalar annihilators at every fixed exponent. -/
theorem powerKernel_flat (b : B) (k : ℕ) :
    powerKernel (R := S) (j b) k =
      (powerKernel (R := R) b k).map (algebraMap R S) := by
  let f := LinearMap.toSpanSingleton R B (b ^ k)
  let I := powerKernel (R := R) b k
  apply le_antisymm
  · intro x hx
    have ht : x ⊗ₜ[R] (b ^ k) = 0 := by
      have h := (mem_powerKernel (j b) k x).mp hx
      rw [← map_pow] at h
      change ((1 : S) ⊗ₜ[R] (b ^ k)) * (x ⊗ₜ[R] (1 : B)) = 0 at h
      simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] using h
    have hz : f.lTensor S (x ⊗ₜ[R] (1 : R)) = 0 := by
      simpa only [LinearMap.lTensor_tmul, f, LinearMap.toSpanSingleton_apply, one_smul]
        using ht
    obtain ⟨z, hz⟩ :=
      (Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map f) _).mp hz
    have hm : ∀ z : S ⊗[R] LinearMap.ker f,
        TensorProduct.rid R S ((LinearMap.ker f).subtype.lTensor S z) ∈
          I.map (algebraMap R S) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul t r =>
        change r.val • t ∈ I.map (algebraMap R S)
        rw [Algebra.smul_def, mul_comm]
        exact Ideal.mul_mem_left _ t (Ideal.mem_map_of_mem _ r.property)
      | add z w hz hw =>
        simpa only [map_add] using Ideal.add_mem _ hz hw
    have h := hm z
    rw [hz] at h
    simpa only [TensorProduct.rid_tmul, one_smul] using h
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    apply (mem_powerKernel (j b) k _).mpr
    have h := (mem_powerKernel b k r).mp hr
    rw [← IsScalarTower.algebraMap_apply R S B',
      Algebra.TensorProduct.algebraMap_apply', ← map_pow]
    change ((1 : S) ⊗ₜ[R] (b ^ k)) * ((1 : S) ⊗ₜ[R] algebraMap R B r) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, h, tmul_zero]

/-- Branch equations descend without increasing their exponent. -/
theorem original_equation_same_power (Q : PrimeSpectrum S) (b : B) (k : ℕ) (x : S)
    (hx : x ∉ Q.asIdeal) (he : (j b) ^ k * algebraMap S B' x = 0) :
    ∃ r : R, r ∉ Q.asIdeal.comap (algebraMap R S) ∧ b ^ k * algebraMap R B r = 0 := by
  have hm := (mem_powerKernel (j b) k x).mpr he
  rw [powerKernel_flat] at hm
  have hn : ¬ powerKernel (R := R) b k ≤ Q.asIdeal.comap (algebraMap R S) := by
    intro h
    exact hx ((Ideal.map_le_iff_le_comap.mpr h) hm)
  obtain ⟨r, hr, hp⟩ := IsConcreteLE.not_le_iff_exists.mp hn
  exact ⟨r, hp, (mem_powerKernel b k r).mp hr⟩

end FLT.Mazur.FlatScalarPowerKernel
