/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralUnitDescent
public import FLT.LocalClassFieldTheory.ContinuousCohomologyColimit

/-!
# Canonical integral units as invariant coefficients

Inclusion identifies the integral units of an intermediate field with the
invariants under its fixing subgroup. For a normal field this identification
intertwines the quotient action and the usual finite-field Galois action.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (R K L : Type) [CommRing R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsGalois K L] (E : IntermediateField K L)

attribute [local instance] integralUnitAction

local notation "ρ" => Representation.ofDistribMulAction ℤ Gal(L/K) (IntegralUnitModule R L)

/-- Inclusion with codomain restricted to the actual invariant submodule. -/
def integralUnitInvariantInclusion : IntegralUnitModule R E →ₗ[ℤ]
    Representation.invariants ((ρ).comp E.fixingSubgroup.subtype) :=
  (integralUnitFieldInclusion R K L E).toAdditive.toIntLinearMap.codRestrict _ fun u =>
    (integralUnit_fixed_iff R K L E _).mpr ⟨Additive.toMul u, rfl⟩

/-- Every invariant coefficient comes from exactly one canonical integral unit. -/
theorem integralUnitInvariantInclusion_bijective :
    Function.Bijective (integralUnitInvariantInclusion R K L E) := by
  constructor
  · intro u v h
    exact integralUnitFieldInclusion_injective R K L E (congrArg Subtype.val h)
  · intro u
    obtain ⟨v, hv⟩ := (integralUnit_fixed_iff R K L E u.val).mp u.property
    exact ⟨Additive.ofMul v, Subtype.ext hv⟩

/-- The invariant coefficients are the canonical integral units of the fixed field. -/
def integralUnitInvariantEquiv : IntegralUnitModule R E ≃ₗ[ℤ]
    Representation.invariants ((ρ).comp E.fixingSubgroup.subtype) :=
  LinearEquiv.ofBijective (integralUnitInvariantInclusion R K L E)
    (integralUnitInvariantInclusion_bijective R K L E)

variable [IsGalois K E]

/-- The quotient Galois group is the automorphism group of the intermediate field. -/
def integralUnitQuotientEquiv : Gal(L/K) ⧸ E.fixingSubgroup ≃* Gal(E/K) :=
  QuotientGroup.liftEquiv E.fixingSubgroup (AlgEquiv.restrictNormalHom_surjective L)
    E.restrictNormalHom_ker.symm

/-- The quotient comparison is ordinary restriction on representatives. -/
@[simp] theorem integralUnitQuotientEquiv_mk (g : Gal(L/K)) :
    integralUnitQuotientEquiv K L E (g : Gal(L/K) ⧸ E.fixingSubgroup) =
      g.restrictNormal E := rfl

/-- Inclusion intertwines the actual field actions. -/
theorem integralUnitFieldInclusion_equivariant (g : Gal(L/K)) (u : IntegralUnitModule R E) :
    integralUnitFieldInclusion R K L E (Additive.toMul (g.restrictNormal E • u)) =
      Additive.toMul (g • Additive.ofMul
        (integralUnitFieldInclusion R K L E (Additive.toMul u))) := by
  apply Units.ext
  apply Subtype.ext
  change ((↑(Additive.toMul (g.restrictNormal E • u)) : integralClosure R E) : L) = _
  rw [integralUnitAction_val R K L]
  have h := integralUnitAction_val R K E (g.restrictNormal E) u
  exact (congrArg (fun x : E => (x : L)) h).trans
    (AlgEquiv.restrictNormal_apply E g _)

/-- The linear equivalence respects the quotient action, not just the underlying modules. -/
theorem integralUnitInvariantEquiv_equivariant (g : Gal(L/K) ⧸ E.fixingSubgroup)
    (u : IntegralUnitModule R E) :
    integralUnitInvariantEquiv R K L E (integralUnitQuotientEquiv K L E g • u) =
      (ρ).quotientToInvariants E.fixingSubgroup g (integralUnitInvariantEquiv R K L E u) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E.fixingSubgroup g
  apply Subtype.ext
  exact integralUnitFieldInclusion_equivariant R K L E g u

end LocalClassFieldTheory
