/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralFixedPoints
public import FLT.GroupScheme.OrdinaryModelFiberPoints

/-!
# Integral points of the actual ordinary quotient

A trivial quotient character supplies the integral point above one on the
contracted quotient itself. Its tensor fibre has precisely the original
vectors projecting to one. Conversely, an integral point above one forces
the quotient character to be trivial over the chosen base field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open GaloisRepresentation.Extensions
namespace ThreeAdicPlan

variable {R K k : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  [IsPrincipalIdealRing R] [Field k]
  (X : FF R K) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) k X.Points]
  {α β : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points) α β)

omit [IsPrincipalIdealRing R] in
/-- The chosen quotient vector descends exactly when its character is trivial. -/
theorem ordinary_integralPoint_one_iff :
    (∃ p : (ordinaryQuotientModel X E).CoordinateRing →ₐ[R] R,
      (Algebra.ofId R (AlgebraicClosure K)).comp p =
        (ordinaryQuotientModel X E).integralPoints (1 : k)) ↔ β = 1 := by
  rw [(ordinaryQuotientModel X E).exists_integralPoint_iff_fixed]
  constructor
  · intro h
    ext g
    have hg := h g
    change (β g : k) * 1 = 1 at hg
    simpa using hg
  · intro h g
    change (β g : k) * 1 = 1
    simp [h]

/-- The integral quotient point corresponding to one, on the actual contracted model. -/
def ordinaryIntegralQuotientPoint (hβ : β = 1) :
    (ordinaryQuotientModel X E).CoordinateRing →ₐ[R] R :=
  ((ordinary_integralPoint_one_iff X E).mpr hβ).choose

omit [IsPrincipalIdealRing R] in
/-- The constructed point has the specified geometric value. -/
theorem ordinaryIntegralQuotientPoint_spec (hβ : β = 1) :
    (Algebra.ofId R (AlgebraicClosure K)).comp (ordinaryIntegralQuotientPoint X E hβ) =
      (ordinaryQuotientModel X E).integralPoints (1 : k) :=
  ((ordinary_integralPoint_one_iff X E).mpr hβ).choose_spec

/-- The actual quotient map defines the coordinate algebra of the middle term. -/
local instance quotientPointAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra

/-- The quotient algebra is compatible with base scalars. -/
local instance quotientPointTower :
    IsScalarTower R (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- The tensor fibre at the constructed integral point has the intended generic vectors. -/
def ordinaryIntegralOneFiberEquiv (hβ : β = 1) :
    (HopfAlgebra.PointFiber (A := X.CoordinateRing)
      (ordinaryIntegralQuotientPoint X E hβ) →ₐ[R] AlgebraicClosure K) ≃
      {x : X.Points // E.projection x = 1} := by
  have e := ordinaryPointFiberEquiv X E (ordinaryIntegralQuotientPoint X E hβ)
  rw [ordinaryIntegralQuotientPoint_spec, Equiv.symm_apply_apply] at e
  exact e

end ThreeAdicPlan
