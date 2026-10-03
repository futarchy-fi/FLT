/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.OpenNormalFixedField
public import FLT.GaloisRepresentation.Extensions.FiniteDescent

/-!
# Finite Galois descent of continuous cocycles

Realize the affine kernel by its fixed field, then transport both the
coefficient action and cocycle to the Galois group of that finite extension.
The inflation identities use the actual restriction homomorphism.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {K L M : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [AddCommGroup M] [DistribMulAction Gal(L/K) M]
    [TopologicalSpace M] [DiscreteTopology M] [Finite M]
    (c : Gal(L/K) → M) (hc : groupCohomology.IsCocycle₁ c) (hcont : Continuous c)
    (hact : ∀ x : M, Continuous (fun g : Gal(L/K) ↦ g • x))

/-- The finite Galois field cutting out both the cocycle and its coefficient action. -/
abbrev cocycleFixedField : FiniteGaloisIntermediateField K L :=
  openNormalFixedField (cocycleOpenNormal c hc hcont hact)

/-- The coefficient action transported to the finite Galois group. -/
@[instance_reducible] noncomputable def finiteGaloisAction :
    DistribMulAction Gal(cocycleFixedField c hc hcont hact/K) M :=
  letI : DistribMulAction
    (Gal(L/K) ⧸ (cocycleOpenNormal c hc hcont hact).toSubgroup) M := descendedAction c hc
  DistribMulAction.compHom M
    (openNormalQuotientEquiv (cocycleOpenNormal c hc hcont hact)).symm.toMonoidHom

/-- The cocycle transported to the finite Galois group. -/
noncomputable def finiteGaloisCocycle (g : Gal(cocycleFixedField c hc hcont hact/K)) : M :=
  descendedCocycle c hc
    ((openNormalQuotientEquiv (cocycleOpenNormal c hc hcont hact)).symm g)

/-- Inflation by restriction recovers the original cocycle. -/
theorem finiteGaloisCocycle_restrict (g : Gal(L/K)) :
    finiteGaloisCocycle c hc hcont hact
      (AlgEquiv.restrictNormalHom (cocycleFixedField c hc hcont hact) g) = c g := by
  unfold finiteGaloisCocycle
  rw [← openNormalQuotientEquiv_mk (cocycleOpenNormal c hc hcont hact),
    MulEquiv.symm_apply_apply]
  exact descendedCocycle_mk c hc g

/-- Inflation by restriction recovers the original coefficient action. -/
theorem finiteGaloisAction_restrict (g : Gal(L/K)) (x : M) :
    letI := finiteGaloisAction c hc hcont hact
    AlgEquiv.restrictNormalHom (cocycleFixedField c hc hcont hact) g • x = g • x := by
  change descendedLinear c hc
    ((openNormalQuotientEquiv (cocycleOpenNormal c hc hcont hact)).symm
      (AlgEquiv.restrictNormalHom (cocycleFixedField c hc hcont hact) g)) x = g • x
  rw [← openNormalQuotientEquiv_mk (cocycleOpenNormal c hc hcont hact),
    MulEquiv.symm_apply_apply]
  exact descendedLinear_mk c hc g x

/-- The finite Galois representative satisfies the cocycle equation. -/
theorem finiteGaloisCocycle_isCocycle :
    letI := finiteGaloisAction c hc hcont hact
    groupCohomology.IsCocycle₁ (finiteGaloisCocycle c hc hcont hact) := by
  let := finiteGaloisAction c hc hcont hact
  intro g h
  let e := openNormalQuotientEquiv (cocycleOpenNormal c hc hcont hact)
  change descendedCocycle c hc (e.symm (g * h)) =
    descendedLinear c hc (e.symm g) (descendedCocycle c hc (e.symm h)) +
      descendedCocycle c hc (e.symm g)
  rw [map_mul]
  exact descendedCocycle_isCocycle c hc (e.symm g) (e.symm h)

/-- The finite Galois cocycle is continuous for the Krull topology. -/
theorem continuous_finiteGaloisCocycle : Continuous (finiteGaloisCocycle c hc hcont hact) :=
  continuous_of_discreteTopology

end GaloisRepresentation.Extensions
