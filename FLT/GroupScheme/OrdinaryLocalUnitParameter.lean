/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryLocalKernelBasis
public import FLT.GroupScheme.HopfPointFiberGradedGenerator

/-!
# Integral unit parameters on the actual ordinary fibre

The diagonalizable comparison supplies every basis prerequisite of the fibre
construction. Strong grading produces a homogeneous unit and its unique
integral power parameter on the original fibre above one.
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
local instance localUnitAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra

/-- The quotient arrow respects the local base. -/
local instance localUnitTower : IsScalarTower (v.adicCompletionIntegers K)
    (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- Faithful flatness is supplied by the constructed ordinary extension. -/
local instance localUnitFaithfullyFlat :
    Module.FaithfullyFlat (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotientFaithfullyFlat

/-- A degree-one homogeneous unit in the actual ordinary fibre. -/
def ordinaryLocalFiberGenerator :
    (PointFiber (A := X.CoordinateRing) (ordinaryIntegralQuotientPoint X E hβ))ˣ :=
  pointFiberGradedGenerator (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    (ordinaryLocalAugmentationBasis v p X E hζ hα he)
    (ordinaryLocalAugmentationBasis_one v p X E hζ hα he)
    (ordinaryLocalAugmentationBasis_mul v p X E hζ hα he)
    (ordinaryLocalAugmentationBasis_diagonal v p X E hζ hα he)
    (Multiplicative.ofAdd (1 : ZMod p))

/-- Its p-th power is a unique integral unit; neither the parameter nor its existence is assumed. -/
theorem ordinaryLocalFiberGenerator_parameter :
    ∃! u : (v.adicCompletionIntegers K)ˣ,
      Units.map (algebraMap (v.adicCompletionIntegers K)
        (PointFiber (A := X.CoordinateRing) (ordinaryIntegralQuotientPoint X E hβ))).toMonoidHom u =
      ordinaryLocalFiberGenerator v p X E hζ hα he hβ ^ p := by
  apply pointFiberGradedGenerator_parameter
  simp [← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero]

/-- The integral parameter constructed from this actual fibre. -/
def ordinaryLocalUnitParameter : (v.adicCompletionIntegers K)ˣ :=
  (ordinaryLocalFiberGenerator_parameter v p X E hζ hα he hβ).choose

/-- The constructed unit satisfies the integral root equation. -/
theorem ordinaryLocalUnitParameter_equation :
    Units.map (algebraMap (v.adicCompletionIntegers K)
      (PointFiber (A := X.CoordinateRing) (ordinaryIntegralQuotientPoint X E hβ))).toMonoidHom
      (ordinaryLocalUnitParameter v p X E hζ hα he hβ) =
        ordinaryLocalFiberGenerator v p X E hζ hα he hβ ^ p :=
  (ordinaryLocalFiberGenerator_parameter v p X E hζ hα he hβ).choose_spec.1

/-- Every original vector above one evaluates the generator to a root of the same integral unit. -/
theorem ordinaryLocalUnitParameter_evaluation (w : X.Points) (hw : E.projection w = 1) :
    Units.map (ordinaryIntegralFiberPoint X E hβ w hw).toMonoidHom
      (ordinaryLocalFiberGenerator v p X E hζ hα he hβ) ^ p =
        Units.map (algebraMap (v.adicCompletionIntegers K)
          (AlgebraicClosure (v.adicCompletion K))).toMonoidHom
          (ordinaryLocalUnitParameter v p X E hζ hα he hβ) := by
  have h := congrArg (Units.map (ordinaryIntegralFiberPoint X E hβ w hw).toMonoidHom)
    (ordinaryLocalUnitParameter_equation v p X E hζ hα he hβ)
  rw [map_pow] at h
  apply Units.ext
  exact (congrArg Units.val h.symm).trans
    ((ordinaryIntegralFiberPoint X E hβ w hw).commutes _)

end ThreeAdicPlan
