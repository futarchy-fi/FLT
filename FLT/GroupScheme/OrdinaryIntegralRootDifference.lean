/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryIntegralFiberCocycle
public import FLT.GaloisRepresentation.Extensions.OrdinaryRootClass

/-!
# Root coordinates of the actual integral fibre difference

The augmentation quotient is identified with the schematic kernel by its
proved ideal equality. The actual fibre difference then recovers the root
cocycle of the original representation. This compares geometric points and
classes; it does not claim a multiplicative integral coordinate presentation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open GaloisRepresentation.Extensions HopfAlgebra KummerTheory
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K] [IsPrincipalIdealRing R]
  {p : ℕ} [Fact p.Prime]
  (X : FF R K) [Module (ZMod p) X.Points]
  [SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (ZMod p) X.Points]
  {α β : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* (ZMod p)ˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction (ZMod p)
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points) α β)

/-- The actual augmentation quotient is the constructed schematic kernel. -/
def ordinaryAugmentationKernelEquiv :
    (X.CoordinateRing ⧸ augmentationIdeal (ordinaryModelExtension X E).quotient) ≃ₐ[R]
      (ordinaryKernelModel X E).CoordinateRing :=
  Ideal.quotientEquivAlgOfEq R
    ((ordinaryGenericInjection X E).quotientKernelIdealEqClosureIdeal
      (ordinaryGenericProjection X E) E.surjective (ordinaryGenericExact X E))

/-- The kernel comparison retains each original coordinate representative. -/
theorem ordinaryAugmentationKernelEquiv_mk (a : X.CoordinateRing) :
    ordinaryAugmentationKernelEquiv X E
      (Ideal.Quotient.mk (augmentationIdeal (ordinaryModelExtension X E).quotient) a) =
        (ordinaryModelExtension X E).inclusion a :=
  Ideal.quotientEquivAlgOfEq_mk R _ a

/-- The actual quotient map supplies the algebra used to form the fibre. -/
local instance rootDifferenceAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra
/-- The quotient algebra action respects the original base scalars. -/
local instance rootDifferenceTower :
    IsScalarTower R (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

variable (hβ : β = 1)

/-- The actual two fibre points define a point on the original integral kernel. -/
def ordinaryIntegralDifferenceOnKernel (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (ordinaryKernelModel X E).CoordinateRing →ₐ[R] AlgebraicClosure K :=
  (pointFiberDifferenceEvaluation (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    (ordinaryIntegralFiberPoint X E hβ w hw)
    (ordinaryIntegralFiberPoint X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g))).comp
        (ordinaryAugmentationKernelEquiv X E).symm.toAlgHom

variable [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  (hρ : ∀ x : X.Points, Continuous (fun g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ g • x))

/-- The kernel point is the coefficient of the original ordinary Hom cocycle. -/
theorem ordinaryIntegralDifferenceOnKernel_eq (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ordinaryIntegralDifferenceOnKernel X E hβ w hw g =
      (ordinaryKernelModel X E).integralPoints
        ((show ZMod p →ₗ[ZMod p] ZMod p from (E.cocycleOf hρ w hw).val g) 1) := by
  have hd := ordinaryIntegralFiberPoint_difference X E hβ hρ w hw g
  rw [ordinary_integralPoints_injection] at hd
  ext a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  have he := (ordinaryAugmentationKernelEquiv X E).symm_apply_apply
    (Ideal.Quotient.mk (augmentationIdeal (ordinaryModelExtension X E).quotient) b)
  rw [ordinaryAugmentationKernelEquiv_mk] at he
  change (pointFiberDifferenceEvaluation (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    (ordinaryIntegralFiberPoint X E hβ w hw)
    (ordinaryIntegralFiberPoint X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g)))
        ((ordinaryAugmentationKernelEquiv X E).symm
          ((ordinaryModelExtension X E).inclusion b)) = _
  rw [he]
  exact AlgHom.congr_fun hd b

variable {ζ : (AlgebraicClosure K)ˣ} (hζ : IsPrimitiveRoot ζ p)
  (hχ : homCharacter α β = primeCyclotomicCharacter (K := K) hζ)

/-- Root coordinates of the actual integral fibre difference equal the constructed root cocycle. -/
theorem ordinaryIntegralDifference_rootCocycle (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    primeRootCoordinates hζ ((ordinaryKernelModel X E).integralPoints.symm
      (ordinaryIntegralDifferenceOnKernel X E hβ w hw g)) =
        (E.rootCocycle hζ α β hχ hρ w hw).val g := by
  rw [ordinaryIntegralDifferenceOnKernel_eq X E hβ hρ, Equiv.symm_apply_apply]
  rfl

end ThreeAdicPlan
