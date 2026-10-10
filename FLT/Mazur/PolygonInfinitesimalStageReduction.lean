/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalStages

/-!
# The actual closed coefficient fiber of a truncated smoothing stage

Evaluation at q = 0 is surjective and has nilpotent kernel. Its spectrum is
therefore a surjective closed immersion, over any commutative coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The actual coefficient reduction q ↦ 0 at every finite order. -/
def reduction : Ring R m →ₐ[R] R :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id R R) 0 (by simp)

@[simp] theorem reduction_parameter : reduction R m (parameter R m) = 0 := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Reduction retains the original constant coefficient. -/
@[simp] theorem reduction_mk (p : R[X]) :
    reduction R m (AdjoinRoot.mk _ p) = p.coeff 0 := by
  simp [reduction, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero]

/-- The original constants give a section of coefficient reduction. -/
theorem reduction_surjective : Function.Surjective (reduction R m) := by
  intro r
  exact ⟨algebraMap R _ r, (reduction R m).commutes r⟩

/-- Every element killed by reduction has the same explicit nilpotence bound. -/
theorem reduction_kernel_pow (z : Ring R m) (hz : reduction R m z = 0) :
    z ^ (m + 1) = 0 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [reduction_mk] at hz
  obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr hz
  rw [map_mul, mul_pow]
  change parameter R m ^ (m + 1) * _ = 0
  rw [parameter_pow, zero_mul]

/-- The coefficient reduction kernel is contained in the nilradical. -/
theorem reduction_kernel_le_nilradical :
    RingHom.ker (reduction R m).toRingHom ≤ nilradical (Ring R m) := by
  intro z hz
  exact (mem_nilradical).mpr ⟨m + 1, reduction_kernel_pow R m z hz⟩

/-- The actual closed coefficient fiber inclusion. -/
def reductionBase : Spec (.of R) ⟶ Spec (.of (Ring R m)) :=
  Spec.map (CommRingCat.ofHom (reduction R m).toRingHom)

instance reductionBase_isClosedImmersion : IsClosedImmersion (reductionBase R m) :=
  IsClosedImmersion.spec_of_surjective _ (reduction_surjective R m)

/-- Nilpotence makes the actual closed coefficient fiber topologically surjective. -/
instance reductionBase_surjective : Surjective (reductionBase R m) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap (reduction R m).toRingHom)
  rw [← Set.range_eq_univ,
    range_comap_of_surjective _ _ (reduction_surjective R m)]
  exact (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr (reduction_kernel_le_nilradical R m)

/-- The coefficient reductions are compatible with successive stage restrictions. -/
theorem reduction_restriction :
    (reduction R m).comp (restriction R m) = reduction R (m + 1) := by
  apply AdjoinRoot.algHom_ext
  simp [parameter, restriction, reduction]

end FLT.Mazur.PolygonInfinitesimalStages
