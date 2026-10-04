/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RootModuleLinear
public import FLT.GaloisRepresentation.Extensions.LinearCoefficientMap

/-!
# Prime-root projections of finite coefficient classes

Every prime-linear functional on the residual coefficient field gives an
equivariant projection of its cyclotomic line to actual roots of unity.
-/

@[expose] public noncomputable section
namespace KummerTheory
open GaloisRepresentation.Extensions

variable {K L k : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] [Field k] [Algebra (ZMod p) k]
  {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) (a : Module.Dual (ZMod p) k)

/-- A residual-field functional followed by primitive-root coordinates. -/
def finiteRootProjection : CharacterModule (primeCyclotomicCharacter (K := K) hζ) k →ₗ[ZMod p]
    RootModule L p :=
  (primeCyclotomicLinearCoordinates (K := K) hζ).toLinearMap.comp a

/-- The functional commutes with the scalar cyclotomic action. -/
theorem finiteRootProjection_equivariant (g : Gal(L/K))
    (x : CharacterModule (primeCyclotomicCharacter (K := K) hζ) k) :
    finiteRootProjection hζ a (g • x) = g • finiteRootProjection hζ a x := by
  change primeCyclotomicCoordinates (K := K) hζ
    (a (algebraMap (ZMod p) k (primeCyclotomicCharacter (K := K) hζ g : ZMod p) *
      (show k from x))) = _
  rw [← Algebra.smul_def, map_smul]
  exact primeCyclotomicCoordinates_equivariant hζ g (a x)

/-- Project an original continuous cyclotomic cocycle, preserving its representative. -/
def finiteRootCocycle
    (c : ContinuousCocycle Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)) :
    ContinuousCocycle Gal(L/K) (RootModule L p) :=
  linearCocycleForget (linearCocycleMap (finiteRootProjection hζ a)
    (finiteRootProjection_equivariant hζ a) (linearCocycleOf (k := ZMod p) c))

/-- Projection on splitting classes is induced by the proved equivariant linear map. -/
def finiteRootClass
    (x : ContinuousClass Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)) :
    ContinuousClass Gal(L/K) (RootModule L p) :=
  linearClassEquiv (linearCoefficientClass (finiteRootProjection hζ a)
    (finiteRootProjection_equivariant hζ a) ((linearClassEquiv (k := ZMod p)).symm x))

/-- On representatives, class projection uses the actual projected cocycle. -/
theorem finiteRootClass_mk
    (c : ContinuousCocycle Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)) :
    finiteRootClass hζ a (continuousClassMk c) = continuousClassMk (finiteRootCocycle hζ a c) := by
  change linearClassEquiv (linearCoefficientClass _ _
    ((linearClassEquiv (k := ZMod p)).symm
      (linearClassEquiv (Submodule.Quotient.mk (linearCocycleOf (k := ZMod p) c))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end KummerTheory
