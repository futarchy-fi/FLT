/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryFiniteUnitParameter

/-!
# The actual ordinary root ratio

Evaluation of the constructed integral generator on two original fibre vectors
recovers the original cocycle, in its prescribed primitive-root coordinates.
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

variable (hβ : β = 1) (a : Module.Dual (ZMod p) k)

/-- The actual quotient arrow defines the fibre algebra. -/
local instance finiteRootRatioAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra

/-- The quotient arrow respects the local base. -/
local instance finiteRootRatioTower : IsScalarTower (v.adicCompletionIntegers K)
    (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- Faithful flatness is supplied by the constructed ordinary extension. -/
local instance finiteRootRatioFaithfullyFlat :
    Module.FaithfullyFlat (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotientFaithfullyFlat

variable [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  (hρ : ∀ x : X.Points, Continuous
    (fun g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K) ↦ g • x))

/-- The evaluated fibre generator's ratio is the root of the original ordinary cocycle. -/
theorem ordinaryFiniteFiberGenerator_ratio (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) :
    Units.map (ordinaryIntegralFiberPoint X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g)).toMonoidHom
        (ordinaryFiniteFiberGenerator v p X E hζ hα he hβ a) /
      Units.map (ordinaryIntegralFiberPoint X E hβ w hw).toMonoidHom
        (ordinaryFiniteFiberGenerator v p X E hζ hα he hβ a) =
      rootUnit (primeRootCoordinates hζ
        (a ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).val g) 1))) := by
  have hd := pointFiberGradedGenerator_difference (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    (ordinaryFiniteAugmentationBasis v p X E hζ hα he)
    (ordinaryFiniteAugmentationBasis_one v p X E hζ hα he)
    (ordinaryFiniteAugmentationBasis_mul v p X E hζ hα he)
    (ordinaryFiniteAugmentationBasis_diagonal v p X E hζ hα he)
    (ordinaryIntegralFiberPoint X E hβ w hw)
    (ordinaryIntegralFiberPoint X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g))
    (Multiplicative.ofAdd a)
  apply Units.ext
  refine (congrArg Units.val hd.symm).trans ?_
  change ordinaryFiniteIntegralDifferenceOnKernel X E hβ w hw g
    (ordinaryFiniteKernelBasis v p X E hζ hα he (Multiplicative.ofAdd a)) = _
  rw [ordinaryFiniteIntegralDifferenceOnKernel_eq X E hβ hρ]
  exact ordinaryFiniteKernelBasis_point v p X E hζ hα he
    ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).val g) 1) a

end ThreeAdicPlan
