/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryIntegralQuotientPoint
public import FLT.GroupScheme.OrdinaryNormalizedDifference

/-!
# The cocycle on the fibre of the constructed integral quotient point

When the quotient character is trivial, both fibre points and their integral
base point are constructed from the original vectors. The Hopf difference
then gives the injected Hom cocycle, without point-comparison hypotheses.
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
local instance fiberCocycleAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra
/-- This coordinate algebra structure respects the base ring. -/
local instance fiberCocycleTower :
    IsScalarTower R (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- The point on the actual integral tensor fibre corresponding to the chosen vector. -/
def ordinaryIntegralFiberPoint (x : X.Points) (hx : E.projection x = 1) :
    PointFiber (A := X.CoordinateRing) (ordinaryIntegralQuotientPoint X E hβ) →ₐ[R]
      AlgebraicClosure K :=
  pointFiberLift (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    ⟨toConv (X.integralPoints x), by
      apply ofConv_injective
      change (X.integralPoints x).comp (ordinaryModelExtension X E).quotient.toAlgHom = _
      rw [← ordinary_integralPoints_projection, hx, ordinaryIntegralQuotientPoint_spec]⟩

/-- Restriction of the constructed fibre point recovers the original vector. -/
theorem ordinaryIntegralFiberPoint_restrict (x : X.Points) (hx : E.projection x = 1) :
    (ordinaryIntegralFiberPoint X E hβ x hx).comp
      (pointFiberMap (ordinaryIntegralQuotientPoint X E hβ)) = X.integralPoints x := by
  have h := pointFiberRestrict_lift (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    (show FiberPoints (ordinaryModelExtension X E).quotient _ from
      ⟨toConv (X.integralPoints x), by
        apply ofConv_injective
        change (X.integralPoints x).comp (ordinaryModelExtension X E).quotient.toAlgHom = _
        rw [← ordinary_integralPoints_projection, hx, ordinaryIntegralQuotientPoint_spec]⟩)
  exact congrArg (fun z ↦ z.val.ofConv) h

include hβ
omit [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K] [IsPrincipalIdealRing R] in
/-- Galois translates stay above the constructed integral quotient point. -/
theorem ordinaryIntegralFiberPoint_translate (x : X.Points) (hx : E.projection x = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : E.projection (g • x) = 1 := by
  simpa [hβ, hx] using E.projection_equivariant g x

variable [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  (hρ : ∀ x : X.Points, Continuous (fun g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ g • x))

/-- The actual fibre difference equals the injected coefficient of the original Hom cocycle. -/
theorem ordinaryIntegralFiberPoint_difference (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (pointFiberDifferenceEvaluation (ordinaryModelExtension X E).quotient (by rfl)
      (ordinaryIntegralQuotientPoint X E hβ)
      (ordinaryIntegralFiberPoint X E hβ w hw)
      (ordinaryIntegralFiberPoint X E hβ (g • w)
        (ordinaryIntegralFiberPoint_translate X E hβ w hw g))).comp
          (Ideal.Quotient.mkₐ R (augmentationIdeal (ordinaryModelExtension X E).quotient)) =
      X.integralPoints (E.injection ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).val g) 1)) := by
  apply ordinary_pointFiberDifference_cocycle X E hρ _ (by rfl) _ _ _ w hw g
  · exact ordinaryIntegralFiberPoint_restrict X E hβ w hw
  · simpa [hβ] using ordinaryIntegralFiberPoint_restrict X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g)

end ThreeAdicPlan
