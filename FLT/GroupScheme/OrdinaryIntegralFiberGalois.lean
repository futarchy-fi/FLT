/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryIntegralFiberCocycle

/-!
# Galois action on the actual integral fibre points

Translation of the original vector is postcomposition of its fibre point
with the field automorphism. The comparison follows by restriction to the
middle coordinate algebra.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open GaloisRepresentation.Extensions WithConv HopfAlgebra
namespace ThreeAdicPlan
variable {R K k : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  [IsPrincipalIdealRing R] [Field k]
  (X : FF R K) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) k X.Points]
  {α β : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points) α β) (hβ : β = 1)

/-- The actual quotient defines the middle coordinate algebra structure. -/
local instance fiberGaloisAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra
/-- This coordinate algebra structure respects the base ring. -/
local instance fiberGaloisTower :
    IsScalarTower R (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- The constructed point above the translated vector is the field translate of the point. -/
theorem ordinaryIntegralFiberPoint_galois (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ordinaryIntegralFiberPoint X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g) =
        (g.toAlgHom.restrictScalars R).comp (ordinaryIntegralFiberPoint X E hβ w hw) := by
  apply (pointFiberPointsEquiv (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)).injective
  apply Subtype.ext
  apply ofConv_injective
  change (ordinaryIntegralFiberPoint X E hβ (g • w) _).comp
      (pointFiberMap (ordinaryIntegralQuotientPoint X E hβ)) =
    ((g.toAlgHom.restrictScalars R).comp (ordinaryIntegralFiberPoint X E hβ w hw)).comp
      (pointFiberMap (ordinaryIntegralQuotientPoint X E hβ))
  rw [AlgHom.comp_assoc, ordinaryIntegralFiberPoint_restrict,
    ordinaryIntegralFiberPoint_restrict, FF.integralPoints_smul]

end ThreeAdicPlan
