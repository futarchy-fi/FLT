/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUniformizer
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RingTheory.Localization.NormTrace

/-!
# Hilbert 90 with an integral unit witness

The integral Hilbert-90 witness can be divided by its uniformizer power.
The base uniformizer is fixed by Galois, so the resulting unit is still a
witness. Unramifiedness is used to prove that the base uniformizer works upstairs.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open scoped nonZeroDivisors

variable (R S K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]

omit [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
  [IsFractionRing S L] [FiniteDimensional K L] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallyUnramified R S] in
/-- Integral and fraction-field norms agree under the base embedding. -/
theorem integral_norm_eq_field_norm (x : S) :
    Algebra.norm K (algebraMap S L x) = algebraMap R K (Algebra.norm R x) := by
  let : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L :=
    IsIntegralClosure.isLocalization R K L S
  exact Algebra.norm_localization R R⁰ x

variable [IsCyclic Gal(L/K)]

omit [IsFractionRing S L] in
/-- A norm-one integral unit is a cyclic coboundary of an integral unit. -/
theorem unramified_unit_hilbert90 (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g)
    (η : Sˣ) (hη : Algebra.norm R (η : S) = 1) :
    ∃ v : Sˣ, Units.map (galRestrict R K L S g).toMonoidHom v / v = η := by
  have hfield : Algebra.norm K (algebraMap S L (η : S)) = 1 := by
    rw [integral_norm_eq_field_norm R S K L, hη, map_one]
  obtain ⟨ε, hε0, hε⟩ := groupCohomology.exists_mul_galRestrict_of_norm_eq_one
    (A := R) (B := S) hg hfield
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hs := unramified_uniformizer_irreducible R S hπ
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hε0 hs
  rw [hu, map_mul, map_pow, (galRestrict R K L S g).commutes] at hε
  have he : (η : S) * galRestrict R K L S g (u : S) = (u : S) :=
    mul_right_cancel₀ (pow_ne_zero n hs.ne_zero) (by simpa only [mul_assoc] using hε)
  have he' : η * Units.map (galRestrict R K L S g).toMonoidHom u = u := Units.ext he
  refine ⟨u⁻¹, ?_⟩
  rw [map_inv, inv_div_inv, div_eq_iff_eq_mul]
  exact he'.symm

end LocalClassFieldTheory
