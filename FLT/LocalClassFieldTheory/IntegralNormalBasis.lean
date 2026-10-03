/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Galois.NormalBasis
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# An integral normal basis of the fraction-field extension

Clearing one base-field denominator in a normal generator gives a normal
K-basis consisting of elements integral over R. It is a basis of a lattice,
not a claim that the full integral closure has a normal integral basis.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open scoped nonZeroDivisors

variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

/-- A K-basis with integral values and the regular Galois permutation law exists. -/
theorem exists_integral_normal_basis :
    ∃ b : Module.Basis Gal(L/K) K L,
      (∀ g, IsIntegral R (b g)) ∧ (∀ g h, g (b h) = b (g * h)) := by
  let b := IsGalois.normalBasis K L
  obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization R⁰ (b 1)
    (Algebra.IsIntegral.isIntegral (R := K) (b 1))
  have hd0 : algebraMap R K (d : R) ≠ 0 :=
    (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
  let u : Kˣ := Units.mk0 (algebraMap R K (d : R)) hd0
  let b' : Module.Basis Gal(L/K) K L := u • b
  have he : ∀ g, b' g = g ((d : R) • b 1) := by
    intro g
    change algebraMap R K (d : R) • b g = g ((d : R) • b 1)
    rw [IsGalois.normalBasis_apply, ← IsScalarTower.algebraMap_smul K (d : R) (b 1)]
    exact (g.toLinearMap.map_smul _ _).symm
  refine ⟨b', fun g => ?_, fun g h => ?_⟩
  · rw [he]
    exact hd.map (g.restrictScalars R).toAlgHom
  · rw [he, he]
    exact rfl

/-- A chosen integral-valued normal K-basis, obtained by denominator clearing. -/
def integralNormalBasis : Module.Basis Gal(L/K) K L :=
  (exists_integral_normal_basis R K L).choose

/-- Every chosen basis vector is integral. -/
theorem integralNormalBasis_integral (g : Gal(L/K)) :
    IsIntegral R (integralNormalBasis R K L g) :=
  (exists_integral_normal_basis R K L).choose_spec.1 g

/-- Galois acts on the basis by the regular permutation action. -/
theorem integralNormalBasis_action (g h : Gal(L/K)) :
    g (integralNormalBasis R K L h) = integralNormalBasis R K L (g * h) :=
  (exists_integral_normal_basis R K L).choose_spec.2 g h

end LocalClassFieldTheory
