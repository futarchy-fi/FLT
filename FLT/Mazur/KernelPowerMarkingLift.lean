/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPowerTorsionLifting

/-!
# Unique kernel corrections restore every marking equation

Choose arbitrary lifts of a finite-exponent marking. If the kernel power map
is bijective, its unique torsion corrections automatically preserve products
and identity. Faithfulness follows from the unchanged original reduction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.KernelPowerMarkingLift
open KernelPowerTorsionLifting
variable {A G H : Type*} [Group A] [CommGroup G] [CommGroup H]
  (ρ : G →* H) (n : ℕ) (hpow : Function.Bijective (fun z : ρ.ker ↦ z ^ n))
  (m : A →* H) (hA : ∀ a : A, a ^ n = 1) (s : A → G) (hs : ∀ a, ρ (s a) = m a)

/-- Correct each chosen lift inside the reduction kernel. -/
def point (a : A) : G :=
  (existsUnique_torsion_lift ρ n hpow (s a) (by rw [hs, ← map_pow, hA, map_one])).choose

/-- Correction retains exactly the prescribed reduced label. -/
theorem point_reduction (a : A) : ρ (point ρ n hpow m hA s hs a) = m a :=
  (existsUnique_torsion_lift ρ n hpow (s a)
    (by rw [hs, ← map_pow, hA, map_one])).choose_spec.1.1.trans (hs a)

/-- Every corrected label satisfies its original finite-exponent equation. -/
theorem point_pow (a : A) : point ρ n hpow m hA s hs a ^ n = 1 :=
  (existsUnique_torsion_lift ρ n hpow (s a)
    (by rw [hs, ← map_pow, hA, map_one])).choose_spec.1.2

/-- Uniqueness forces the corrected labels to preserve the whole group law. -/
def marking : A →* G where
  toFun := point ρ n hpow m hA s hs
  map_one' := torsion_lift_unique ρ n hpow.1 (point_pow ρ n hpow m hA s hs 1)
    (one_pow n) (by rw [point_reduction, map_one, map_one])
  map_mul' a b := by
    apply torsion_lift_unique ρ n hpow.1 (point_pow ρ n hpow m hA s hs (a * b))
    · rw [mul_pow, point_pow, point_pow, one_mul]
    · rw [point_reduction, map_mul, map_mul, point_reduction, point_reduction]

/-- The corrected whole marking reduces to the original homomorphism. -/
theorem reduction_marking : ρ.comp (marking ρ n hpow m hA s hs) = m :=
  MonoidHom.ext (point_reduction ρ n hpow m hA s hs)

/-- A faithful residue marking remains faithful after correction. -/
theorem marking_injective (hm : Function.Injective m) :
    Function.Injective (marking ρ n hpow m hA s hs) := by
  apply Function.Injective.of_comp (f := ρ)
  simpa only [← MonoidHom.coe_comp, reduction_marking] using hm

/-- The corrected marking is independent of all the initial lift choices. -/
theorem marking_unique (q : A →* G) (hq : ρ.comp q = m) :
    q = marking ρ n hpow m hA s hs := by
  apply MonoidHom.ext
  intro a
  apply torsion_lift_unique ρ n hpow.1
  · rw [← map_pow, hA, map_one]
  · exact point_pow ρ n hpow m hA s hs a
  · exact (DFunLike.congr_fun hq a).trans (point_reduction ρ n hpow m hA s hs a).symm

end FLT.Mazur.KernelPowerMarkingLift
