/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryLocalUnitParameter

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

variable (hβ : β = 1)

/-- The actual quotient arrow defines the fibre algebra. -/
local instance localRootRatioAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra

/-- The quotient arrow respects the local base. -/
local instance localRootRatioTower : IsScalarTower (v.adicCompletionIntegers K)
    (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- Faithful flatness is supplied by the constructed ordinary extension. -/
local instance localRootRatioFaithfullyFlat :
    Module.FaithfullyFlat (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotientFaithfullyFlat

variable [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  (hρ : ∀ x : X.Points, Continuous
    (fun g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K) ↦ g • x))

/-- The evaluated fibre generator's ratio is the root of the original ordinary cocycle. -/
theorem ordinaryLocalFiberGenerator_ratio (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) :
    Units.map (ordinaryIntegralFiberPoint X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g)).toMonoidHom
        (ordinaryLocalFiberGenerator v p X E hζ hα he hβ) /
      Units.map (ordinaryIntegralFiberPoint X E hβ w hw).toMonoidHom
        (ordinaryLocalFiberGenerator v p X E hζ hα he hβ) =
      rootUnit (primeRootCoordinates hζ
        ((show ZMod p →ₗ[ZMod p] ZMod p from (E.cocycleOf hρ w hw).val g) 1)) := by
  have hd := pointFiberGradedGenerator_difference (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    (ordinaryLocalAugmentationBasis v p X E hζ hα he)
    (ordinaryLocalAugmentationBasis_one v p X E hζ hα he)
    (ordinaryLocalAugmentationBasis_mul v p X E hζ hα he)
    (ordinaryLocalAugmentationBasis_diagonal v p X E hζ hα he)
    (ordinaryIntegralFiberPoint X E hβ w hw)
    (ordinaryIntegralFiberPoint X E hβ (g • w)
      (ordinaryIntegralFiberPoint_translate X E hβ w hw g))
    (Multiplicative.ofAdd (1 : ZMod p))
  apply Units.ext
  refine (congrArg Units.val hd.symm).trans ?_
  change ordinaryIntegralDifferenceOnKernel X E hβ w hw g
    (ordinaryLocalKernelBasis v p X E hζ hα he (Multiplicative.ofAdd 1)) = _
  rw [ordinaryIntegralDifferenceOnKernel_eq X E hβ hρ]
  simpa only [mul_one] using ordinaryLocalKernelBasis_point v p X E hζ hα he
    ((show ZMod p →ₗ[ZMod p] ZMod p from (E.cocycleOf hρ w hw).val g) 1) 1

end ThreeAdicPlan
