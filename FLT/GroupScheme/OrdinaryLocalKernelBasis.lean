/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryLocalDiagonalKernel
public import FLT.GroupScheme.OrdinaryIntegralRootDifference
public import FLT.GroupScheme.QuotientGroupBasisTransport

/-!
# The group-like basis of the actual ordinary kernel

The integral comparison transports the standard basis to the schematic kernel
and to the augmentation quotient used by the actual ordinary fibre torsor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HopfAlgebra
open NumberField IsLocalRing GaloisRepresentation.Extensions KummerTheory
namespace ThreeAdicPlan

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module (ZMod p) X.Points]
  [SMulCommClass (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) (ZMod p) X.Points]
  {α β : (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) →* (ZMod p)ˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction (ZMod p)
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points) α β)
  {ζ : (AlgebraicClosure (v.adicCompletion K))ˣ} (hζ : IsPrimitiveRoot ζ p)
  (hα : α = primeCyclotomicCharacter hζ)

local instance : IsDedekindDomain (v.adicCompletionIntegers K) :=
  IsPrincipalIdealRing.isDedekindDomain _

variable (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

/-- The actual integral kernel's basis, with primitive-root point normalization. -/
def ordinaryLocalKernelBasis :
    Module.Basis (Multiplicative (ZMod p)) (v.adicCompletionIntegers K)
      (ordinaryKernelModel X E).CoordinateRing :=
  CoactionBasis.transportedGroupBasis (ordinaryLocalDiagonalIso v p X E hζ hα he)

/-- The basis on the actual augmentation quotient used by the fibre torsor. -/
def ordinaryLocalAugmentationBasis :
    Module.Basis (Multiplicative (ZMod p)) (v.adicCompletionIntegers K)
      (X.CoordinateRing ⧸ augmentationIdeal (ordinaryModelExtension X E).quotient) :=
  CoactionBasis.quotientGroupBasis _ (ordinaryAugmentationKernelEquiv X E)
    (ordinaryLocalDiagonalIso v p X E hζ hα he)

/-- Its identity degree is the original quotient unit. -/
theorem ordinaryLocalAugmentationBasis_one :
    ordinaryLocalAugmentationBasis v p X E hζ hα he 1 = 1 :=
  CoactionBasis.quotientGroupBasis_one _ _ _

/-- Its group law is the original quotient multiplication. -/
theorem ordinaryLocalAugmentationBasis_mul (i j : Multiplicative (ZMod p)) :
    ordinaryLocalAugmentationBasis v p X E hζ hα he (i * j) =
      ordinaryLocalAugmentationBasis v p X E hζ hα he i *
        ordinaryLocalAugmentationBasis v p X E hζ hα he j :=
  CoactionBasis.quotientGroupBasis_mul _ _ _ i j

/-- Its diagonal is induced by the actual middle Hopf algebra. -/
theorem ordinaryLocalAugmentationBasis_diagonal :
    CoactionBasis.diagonal (ordinaryLocalAugmentationBasis v p X E hζ hα he) ∘ₗ
      (Ideal.Quotient.mkₐ (v.adicCompletionIntegers K)
        (augmentationIdeal (ordinaryModelExtension X E).quotient)).toLinearMap =
      TensorProduct.map (Ideal.Quotient.mkₐ (v.adicCompletionIntegers K)
        (augmentationIdeal (ordinaryModelExtension X E).quotient)).toLinearMap
        (Ideal.Quotient.mkₐ (v.adicCompletionIntegers K)
          (augmentationIdeal (ordinaryModelExtension X E).quotient)).toLinearMap ∘ₗ
          Coalgebra.comul :=
  CoactionBasis.quotientGroupBasis_diagonal _ (ordinaryAugmentationKernelEquiv X E)
    (ordinaryModelExtension X E).inclusion (ordinaryAugmentationKernelEquiv_mk X E)
    (ordinaryLocalDiagonalIso v p X E hζ hα he)

/-- Kernel point evaluation on the transported basis is the chosen primitive-root power. -/
theorem ordinaryLocalKernelBasis_point (x a : ZMod p) :
    (ordinaryKernelModel X E).integralPoints x
      (ordinaryLocalKernelBasis v p X E hζ hα he (Multiplicative.ofAdd a)) =
        (rootUnit (primeRootCoordinates hζ (x * a)) : AlgebraicClosure (v.adicCompletion K)) :=
  ordinaryLocalDiagonalIso_single v p X E hζ hα he x a

end ThreeAdicPlan
