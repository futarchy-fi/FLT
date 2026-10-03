/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Base-field units as finite Galois invariants

Units fixed by every Galois automorphism descend to the base field. Under
this identification the representation norm is the algebraic field norm.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

local notation "M" => Rep.ofAlgebraAutOnUnits K L

/-- Inclusion of base-field units in the Galois invariant coefficient module. -/
def finiteUnitInvariantInclusion : Additive Kˣ →ₗ[ℤ] (M).ρ.invariants :=
  (Units.map (algebraMap K L).toMonoidHom).toAdditive.toIntLinearMap.codRestrict _ fun u g => by
    apply Additive.toMul.injective
    apply Units.ext
    exact g.commutes (Additive.toMul u : Kˣ)

/-- Inclusion of base-field units is injective. -/
theorem finiteUnitInvariantInclusion_injective :
    Function.Injective (finiteUnitInvariantInclusion K L) := by
  intro u v h
  apply Additive.toMul.injective
  apply Units.ext
  apply (algebraMap K L).injective
  exact congrArg (fun w : (M).ρ.invariants => ((Additive.toMul w.val : Lˣ) : L)) h

variable [IsGalois K L] [FiniteDimensional K L]

/-- Every fixed unit, including its inverse, descends to the base field. -/
theorem finiteUnitInvariantInclusion_surjective :
    Function.Surjective (finiteUnitInvariantInclusion K L) := by
  intro u
  have hx : ((Additive.toMul u.val : Lˣ) : L) ∈ Set.range (algebraMap K L) := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro g
    exact congrArg (fun w : Additive Lˣ => ((Additive.toMul w : Lˣ) : L)) (u.property g)
  obtain ⟨x, hx⟩ := hx
  have hn : x ≠ 0 := by
    intro h
    exact (Additive.toMul u.val : Lˣ).ne_zero (hx.symm.trans (by rw [h, map_zero]))
  refine ⟨Additive.ofMul (Units.mk0 x hn), ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  exact Units.ext hx

/-- Base-field units and finite Galois invariant coefficients are canonically equivalent. -/
def finiteUnitInvariantEquiv : Additive Kˣ ≃ₗ[ℤ] (M).ρ.invariants :=
  LinearEquiv.ofBijective (finiteUnitInvariantInclusion K L)
    ⟨finiteUnitInvariantInclusion_injective K L, finiteUnitInvariantInclusion_surjective K L⟩

/-- The representation norm is the included algebraic norm on units. -/
theorem finiteUnitInvariant_norm (v : Lˣ) :
    (finiteUnitInvariantInclusion K L (Additive.ofMul (Units.map (Algebra.norm K) v)) : M) =
      (M).norm.hom (Additive.ofMul v) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact (groupCohomology.norm_ofAlgebraAutOnUnits_eq v).symm

end LocalClassFieldTheory
