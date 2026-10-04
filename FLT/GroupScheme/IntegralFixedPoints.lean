/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralModelPoints
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral points from fixed generic points

For a finite flat model over an integrally closed domain, every Galois-fixed
geometric point extends uniquely to a point over the base ring. No integral
étaleness or classification of the model is required.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField K]

/-- A fixed geometric coordinate integral over the base belongs to the base ring. -/
theorem integral_fixed_coordinate (z : AlgebraicClosure K) (hz : IsIntegral R z)
    (hfix : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g z = z) :
    ∃ r : R, algebraMap R (AlgebraicClosure K) r = z := by
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed z).mpr hfix
  have hi : IsIntegral R a := (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom R K (AlgebraicClosure K)) (algebraMap K _).injective).mp
      (ha.symm ▸ hz)
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact ⟨r, by rw [IsScalarTower.algebraMap_apply R K, hr, ha]⟩

/-- A fixed point extends to the specified integral coordinate ring, uniquely. -/
theorem FF.exists_unique_integralPoint (X : FF R K) (x : X.Points)
    (hx : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g • x = x) :
    ∃! p : X.CoordinateRing →ₐ[R] R,
      (Algebra.ofId R (AlgebraicClosure K)).comp p = X.integralPoints x := by
  have hr (a : X.CoordinateRing) :
      ∃ r : R, algebraMap R (AlgebraicClosure K) r = X.integralPoints x a := by
    apply integral_fixed_coordinate _ ((Algebra.IsIntegral.isIntegral a).map (X.integralPoints x))
    intro g
    have h := AlgHom.congr_fun (X.integralPoints_smul g x) a
    rw [hx g] at h
    exact h.symm
  let f (a : X.CoordinateRing) : R := (hr a).choose
  have hf (a) : algebraMap R (AlgebraicClosure K) (f a) = X.integralPoints x a :=
    (hr a).choose_spec
  have hinj : Function.Injective (algebraMap R (AlgebraicClosure K)) :=
    (algebraMap K _).injective.comp (IsFractionRing.injective R K)
  let p : X.CoordinateRing →ₐ[R] R :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun a b ↦ hinj (by rw [hf, map_add, map_add, hf, hf])
      map_mul' := fun a b ↦ hinj (by rw [hf, map_mul, map_mul, hf, hf])
      commutes' := fun r ↦ hinj (by rw [hf, AlgHom.commutes]; rfl) }
  refine ⟨p, AlgHom.ext hf, ?_⟩
  intro q hq
  ext a
  apply hinj
  exact (AlgHom.congr_fun hq a).trans (hf a).symm

/-- Integral points of the specified model are exactly its fixed geometric points. -/
theorem FF.exists_integralPoint_iff_fixed (X : FF R K) (x : X.Points) :
    (∃ p : X.CoordinateRing →ₐ[R] R,
      (Algebra.ofId R (AlgebraicClosure K)).comp p = X.integralPoints x) ↔
      ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g • x = x := by
  constructor
  · rintro ⟨p, hp⟩ g
    apply X.integralPoints.injective
    rw [X.integralPoints_smul, ← hp]
    ext a
    exact g.commutes ((algebraMap R K) (p a))
  · intro hx
    exact (X.exists_unique_integralPoint x hx).exists

end ThreeAdicPlan
