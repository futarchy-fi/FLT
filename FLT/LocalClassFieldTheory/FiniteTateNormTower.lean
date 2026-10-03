/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteUnitInvariants
public import FLT.LocalClassFieldTheory.TateInvariantClass
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# The finite field norm quotient in a tower

Norm transitivity constructs the surjection between the actual degree-zero
Tate groups. Its invariant-class formula retains the same base-field unit.
No compatibility with the negative fundamental cup is asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable (K E L : Type) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [IsGalois K E] [IsGalois K L] [FiniteDimensional K E] [FiniteDimensional K L]

local notation "ME" => Rep.ofAlgebraAutOnUnits K E
local notation "ML" => Rep.ofAlgebraAutOnUnits K L

omit [IsGalois K E] [IsGalois K L] [FiniteDimensional K L] in
/-- Transitivity of the actual algebraic norm on units. -/
theorem unitNorm_tower (v : Lˣ) :
    Units.map (Algebra.norm K) (Units.map (Algebra.norm E) v) =
      Units.map (Algebra.norm K) v := by
  apply Units.ext
  exact Algebra.norm_norm (R := K) (S := E) (a := (v : L))

/-- The invariant identification in a tower keeps the base-field unit fixed. -/
def finiteTowerInvariantEquiv : (ML).ρ.invariants ≃ₗ[ℤ] (ME).ρ.invariants :=
  (finiteUnitInvariantEquiv K L).symm.trans (finiteUnitInvariantEquiv K E)

omit [Algebra E L] [IsScalarTower K E L] in
/-- The invariant identification sends included units to the same included units. -/
theorem finiteTowerInvariantEquiv_unit (u : Additive Kˣ) :
    finiteTowerInvariantEquiv K E L (finiteUnitInvariantInclusion K L u) =
      finiteUnitInvariantInclusion K E u := by
  exact congrArg (finiteUnitInvariantEquiv K E)
    ((finiteUnitInvariantEquiv K L).symm_apply_apply u)

/-- Norm transitivity carries the larger field's norm kernel into the smaller field's. -/
theorem finiteTowerInvariant_class_kernel :
    LinearMap.ker (tateInvariantClass ML).hom ≤
      LinearMap.ker
        ((tateInvariantClass ME).hom.comp (finiteTowerInvariantEquiv K E L).toLinearMap) := by
  intro x hx
  obtain ⟨y, hy⟩ := (tateInvariantClass_eq_zero_iff ML x).mp hx
  have he : x = finiteUnitInvariantInclusion K L
      (Additive.ofMul (Units.map (Algebra.norm K) (Additive.toMul (y : Additive Lˣ)))) :=
    Subtype.ext (hy.symm.trans
      (finiteUnitInvariant_norm K L (Additive.toMul (y : Additive Lˣ))).symm)
  subst x
  change tateInvariantClass ME (finiteTowerInvariantEquiv K E L _) = 0
  rw [finiteTowerInvariantEquiv_unit, ← unitNorm_tower K E L (Additive.toMul (y : Additive Lˣ))]
  exact (tateInvariantClass_eq_zero_iff ME _).mpr
    ⟨Additive.ofMul (Units.map (Algebra.norm E) (Additive.toMul (y : Additive Lˣ))),
      (finiteUnitInvariant_norm K E _).symm⟩

/-- The surjection of actual finite-field Tate norm quotients in a tower. -/
def finiteTateNormTower : tateCohomology ML 0 →ₗ[ℤ] tateCohomology ME 0 :=
  ((LinearMap.ker (tateInvariantClass ML).hom).liftQ
    ((tateInvariantClass ME).hom.comp (finiteTowerInvariantEquiv K E L).toLinearMap)
    (finiteTowerInvariant_class_kernel K E L)).comp
      ((tateInvariantClass ML).hom.quotKerEquivOfSurjective
        (tateInvariantClass_surjective ML)).symm.toLinearMap

/-- The tower projection preserves the base-field unit representing a Tate class. -/
theorem finiteTateNormTower_unit (u : Additive Kˣ) :
    finiteTateNormTower K E L (tateInvariantClass ML (finiteUnitInvariantInclusion K L u)) =
      tateInvariantClass ME (finiteUnitInvariantInclusion K E u) := by
  simp only [finiteTateNormTower, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  rw [finiteTowerInvariantEquiv_unit]

/-- The actual finite-field tower projection is surjective. -/
theorem finiteTateNormTower_surjective : Function.Surjective (finiteTateNormTower K E L) := by
  intro a
  obtain ⟨x, rfl⟩ := tateInvariantClass_surjective ME a
  obtain ⟨u, rfl⟩ := finiteUnitInvariantInclusion_surjective K E x
  exact ⟨tateInvariantClass ML (finiteUnitInvariantInclusion K L u),
    finiteTateNormTower_unit K E L u⟩

end LocalClassFieldTheory
