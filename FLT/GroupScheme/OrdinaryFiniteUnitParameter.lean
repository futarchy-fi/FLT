/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryFiniteKernelBasis
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
local instance finiteUnitAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra

/-- The quotient arrow respects the local base. -/
local instance finiteUnitTower : IsScalarTower (v.adicCompletionIntegers K)
    (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- Faithful flatness is supplied by the constructed ordinary extension. -/
local instance finiteUnitFaithfullyFlat :
    Module.FaithfullyFlat (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotientFaithfullyFlat

/-- A homogeneous unit of the specified dual degree in the actual ordinary fibre. -/
def ordinaryFiniteFiberGenerator :
    (PointFiber (A := X.CoordinateRing) (ordinaryIntegralQuotientPoint X E hβ))ˣ :=
  pointFiberGradedGenerator (ordinaryModelExtension X E).quotient (by rfl)
    (ordinaryIntegralQuotientPoint X E hβ)
    (ordinaryFiniteAugmentationBasis v p X E hζ hα he)
    (ordinaryFiniteAugmentationBasis_one v p X E hζ hα he)
    (ordinaryFiniteAugmentationBasis_mul v p X E hζ hα he)
    (ordinaryFiniteAugmentationBasis_diagonal v p X E hζ hα he)
    (Multiplicative.ofAdd a)

/-- Its p-th power is a unique integral unit; neither the parameter nor its existence is assumed. -/
theorem ordinaryFiniteFiberGenerator_parameter :
    ∃! u : (v.adicCompletionIntegers K)ˣ,
      Units.map (algebraMap (v.adicCompletionIntegers K)
        (PointFiber (A := X.CoordinateRing) (ordinaryIntegralQuotientPoint X E hβ))).toMonoidHom u =
      ordinaryFiniteFiberGenerator v p X E hζ hα he hβ a ^ p := by
  apply pointFiberGradedGenerator_parameter
  simp [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), CharP.cast_eq_zero]

/-- The integral parameter constructed from this actual fibre. -/
def ordinaryFiniteUnitParameter : (v.adicCompletionIntegers K)ˣ :=
  (ordinaryFiniteFiberGenerator_parameter v p X E hζ hα he hβ a).choose

/-- The constructed unit satisfies the integral root equation. -/
theorem ordinaryFiniteUnitParameter_equation :
    Units.map (algebraMap (v.adicCompletionIntegers K)
      (PointFiber (A := X.CoordinateRing) (ordinaryIntegralQuotientPoint X E hβ))).toMonoidHom
      (ordinaryFiniteUnitParameter v p X E hζ hα he hβ a) =
        ordinaryFiniteFiberGenerator v p X E hζ hα he hβ a ^ p :=
  (ordinaryFiniteFiberGenerator_parameter v p X E hζ hα he hβ a).choose_spec.1

/-- Every original vector above one evaluates the generator to a root of the same integral unit. -/
theorem ordinaryFiniteUnitParameter_evaluation (w : X.Points) (hw : E.projection w = 1) :
    Units.map (ordinaryIntegralFiberPoint X E hβ w hw).toMonoidHom
      (ordinaryFiniteFiberGenerator v p X E hζ hα he hβ a) ^ p =
        Units.map (algebraMap (v.adicCompletionIntegers K)
          (AlgebraicClosure (v.adicCompletion K))).toMonoidHom
          (ordinaryFiniteUnitParameter v p X E hζ hα he hβ a) := by
  have h := congrArg (Units.map (ordinaryIntegralFiberPoint X E hβ w hw).toMonoidHom)
    (ordinaryFiniteUnitParameter_equation v p X E hζ hα he hβ a)
  rw [map_pow] at h
  apply Units.ext
  exact (congrArg Units.val h.symm).trans
    ((ordinaryIntegralFiberPoint X E hβ w hw).commutes _)

end ThreeAdicPlan
