/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryIntegralFiberCocycle

/-!
# The actual fibre difference over an arbitrary coefficient field

The augmentation quotient is identified with the schematic kernel by its
proved ideal equality. The actual fibre difference then recovers the root
coefficient of the original representation, for any residual coefficient field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open GaloisRepresentation.Extensions HopfAlgebra
namespace ThreeAdicPlan

variable {R K k : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K] [IsPrincipalIdealRing R]
  [Field k]
  (X : FF R K) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) k X.Points]
  {α β : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points) α β)

/-- The actual augmentation quotient is the constructed schematic kernel. -/
def ordinaryFiniteAugmentationKernelEquiv :
    (X.CoordinateRing ⧸ augmentationIdeal (ordinaryModelExtension X E).quotient) ≃ₐ[R]
      (ordinaryKernelModel X E).CoordinateRing :=
  Ideal.quotientEquivAlgOfEq R
    ((ordinaryGenericInjection X E).quotientKernelIdealEqClosureIdeal
      (ordinaryGenericProjection X E) E.surjective (ordinaryGenericExact X E))

/-- The kernel comparison retains each original coordinate representative. -/
theorem ordinaryFiniteAugmentationKernelEquiv_mk (a : X.CoordinateRing) :
    ordinaryFiniteAugmentationKernelEquiv X E
      (Ideal.Quotient.mk (augmentationIdeal (ordinaryModelExtension X E).quotient) a) =
        (ordinaryModelExtension X E).inclusion a :=
  Ideal.quotientEquivAlgOfEq_mk R _ a

/-- The actual quotient map supplies the algebra used to form the fibre. -/
local instance finiteDifferenceAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra
/-- The quotient algebra action respects the original base scalars. -/
local instance finiteDifferenceTower :
    IsScalarTower R (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

variable (hβ : β = 1)

/-- The actual two fibre points define a point on the original integral kernel. -/
def ordinaryFiniteIntegralDifferenceOnKernel (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (ordinaryKernelModel X E).CoordinateRing →ₐ[R] AlgebraicClosure K :=
  (pointFiberDifferenceEvaluation (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    (ordinaryIntegralFiberPoint X E hβ w hw)
    (ordinaryIntegralFiberPoint X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g))).comp
        (ordinaryFiniteAugmentationKernelEquiv X E).symm.toAlgHom

variable [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  (hρ : ∀ x : X.Points, Continuous (fun g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ g • x))

/-- The kernel point is the coefficient of the original ordinary Hom cocycle. -/
theorem ordinaryFiniteIntegralDifferenceOnKernel_eq (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ordinaryFiniteIntegralDifferenceOnKernel X E hβ w hw g =
      (ordinaryKernelModel X E).integralPoints
        ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).val g) 1) := by
  have hd := ordinaryIntegralFiberPoint_difference X E hβ hρ w hw g
  rw [ordinary_integralPoints_injection] at hd
  ext a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  have he := (ordinaryFiniteAugmentationKernelEquiv X E).symm_apply_apply
    (Ideal.Quotient.mk (augmentationIdeal (ordinaryModelExtension X E).quotient) b)
  rw [ordinaryFiniteAugmentationKernelEquiv_mk] at he
  change (pointFiberDifferenceEvaluation (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    (ordinaryIntegralFiberPoint X E hβ w hw)
    (ordinaryIntegralFiberPoint X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g)))
        ((ordinaryFiniteAugmentationKernelEquiv X E).symm
          ((ordinaryModelExtension X E).inclusion b)) = _
  rw [he]
  exact AlgHom.congr_fun hd b

end ThreeAdicPlan
