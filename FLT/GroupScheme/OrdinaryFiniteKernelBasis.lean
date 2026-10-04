/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryFiniteDiagonalKernel
public import FLT.GroupScheme.OrdinaryFiniteFiberDifference
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

variable {K k : Type} [Field K] [NumberField K] [Field k] [Finite k]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (X : FF (v.adicCompletionIntegers K) (v.adicCompletion K)) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) k X.Points]
  {α β : (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) X.Points) α β)
  {ζ : (AlgebraicClosure (v.adicCompletion K))ˣ} (hζ : IsPrimitiveRoot ζ p)
  (hα : α = (Units.map (algebraMap (ZMod p) k).toMonoidHom).comp
    (primeCyclotomicCharacter hζ))

local instance : Finite (Module.Dual (ZMod p) k) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

local instance : IsDedekindDomain (v.adicCompletionIntegers K) :=
  IsPrincipalIdealRing.isDedekindDomain _

variable (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)

/-- The actual integral kernel's basis, with primitive-root point normalization. -/
def ordinaryFiniteKernelBasis :
    Module.Basis (Multiplicative (Module.Dual (ZMod p) k)) (v.adicCompletionIntegers K)
      (ordinaryKernelModel X E).CoordinateRing :=
  CoactionBasis.transportedGroupBasis (ordinaryFiniteDiagonalIso v p X E hζ hα he)

/-- The basis on the actual augmentation quotient used by the fibre torsor. -/
def ordinaryFiniteAugmentationBasis :
    Module.Basis (Multiplicative (Module.Dual (ZMod p) k)) (v.adicCompletionIntegers K)
      (X.CoordinateRing ⧸ augmentationIdeal (ordinaryModelExtension X E).quotient) :=
  CoactionBasis.quotientGroupBasis _ (ordinaryFiniteAugmentationKernelEquiv X E)
    (ordinaryFiniteDiagonalIso v p X E hζ hα he)

/-- Its identity degree is the original quotient unit. -/
theorem ordinaryFiniteAugmentationBasis_one :
    ordinaryFiniteAugmentationBasis v p X E hζ hα he 1 = 1 :=
  CoactionBasis.quotientGroupBasis_one _ _ _

/-- Its group law is the original quotient multiplication. -/
theorem ordinaryFiniteAugmentationBasis_mul (i j : Multiplicative (Module.Dual (ZMod p) k)) :
    ordinaryFiniteAugmentationBasis v p X E hζ hα he (i * j) =
      ordinaryFiniteAugmentationBasis v p X E hζ hα he i *
        ordinaryFiniteAugmentationBasis v p X E hζ hα he j :=
  CoactionBasis.quotientGroupBasis_mul _ _ _ i j

/-- Its diagonal is induced by the actual middle Hopf algebra. -/
theorem ordinaryFiniteAugmentationBasis_diagonal :
    CoactionBasis.diagonal (ordinaryFiniteAugmentationBasis v p X E hζ hα he) ∘ₗ
      (Ideal.Quotient.mkₐ (v.adicCompletionIntegers K)
        (augmentationIdeal (ordinaryModelExtension X E).quotient)).toLinearMap =
      TensorProduct.map (Ideal.Quotient.mkₐ (v.adicCompletionIntegers K)
        (augmentationIdeal (ordinaryModelExtension X E).quotient)).toLinearMap
        (Ideal.Quotient.mkₐ (v.adicCompletionIntegers K)
          (augmentationIdeal (ordinaryModelExtension X E).quotient)).toLinearMap ∘ₗ
          Coalgebra.comul :=
  CoactionBasis.quotientGroupBasis_diagonal _ (ordinaryFiniteAugmentationKernelEquiv X E)
    (ordinaryModelExtension X E).inclusion (ordinaryFiniteAugmentationKernelEquiv_mk X E)
    (ordinaryFiniteDiagonalIso v p X E hζ hα he)

/-- Kernel point evaluation on the transported basis is the chosen primitive-root power. -/
theorem ordinaryFiniteKernelBasis_point (x : k) (a : Module.Dual (ZMod p) k) :
    (ordinaryKernelModel X E).integralPoints x
      (ordinaryFiniteKernelBasis v p X E hζ hα he (Multiplicative.ofAdd a)) =
        (rootUnit (primeRootCoordinates hζ (a x)) : AlgebraicClosure (v.adicCompletion K)) :=
  ordinaryFiniteDiagonalIso_single v p X E hζ hα he x a

end ThreeAdicPlan
