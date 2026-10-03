/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PrimeUnitSubspace
public import FLT.GaloisRepresentation.Extensions.LinearCoefficientMap

/-!
# Extending the Kummer unit subspace

The coefficient map is constructed from prime cyclotomic coordinates and
the field embedding. The extended subspace is the span of the image of
the independently defined prime unit subspace; it uses no residual-field basis.
-/

@[expose] public section

namespace KummerTheory

open GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (k : Type*) [Field k] [Algebra (ZMod p) k]

/-- The actual extension of root coefficients to a residual-field cyclotomic line. -/
noncomputable def rootCoefficientExtension : RootModule L p →ₛₗ[algebraMap (ZMod p) k]
    CharacterModule (primeCyclotomicCharacter (K := K) hζ) k where
  toFun x := algebraMap (ZMod p) k ((primeCyclotomicLinearCoordinates (K := K) hζ).symm x)
  map_add' x y := by
    change algebraMap (ZMod p) k ((primeCyclotomicLinearCoordinates (K := K) hζ).symm (x + y)) = _
    rw [map_add]
    exact map_add (algebraMap (ZMod p) k) _ _
  map_smul' a x := by
    change algebraMap (ZMod p) k ((primeCyclotomicLinearCoordinates (K := K) hζ).symm (a • x)) = _
    rw [map_smul]
    exact map_mul (algebraMap (ZMod p) k) a _

/-- The constructed extension map intertwines the natural root and cyclotomic actions. -/
theorem rootCoefficientExtension_equivariant (g : Gal(L/K)) (x : RootModule L p) :
    rootCoefficientExtension (K := K) hζ k (g • x) =
      g • rootCoefficientExtension (K := K) hζ k x := by
  change characterCoefficientInclusion (primeCyclotomicCharacter (K := K) hζ) k
    ((primeCyclotomicCoordinates (K := K) hζ).symm (g • x)) = _
  rw [coefficient_symm_equivariant _ (primeCyclotomicCoordinates_equivariant hζ)]
  exact characterCoefficientInclusion_equivariant _ k g _

/-- Scalar extension on continuous root classes, constructed from representatives. -/
noncomputable def extendRootClass :
    LinearContinuousClass (ZMod p) Gal(L/K) (RootModule L p) →ₛₗ[algebraMap (ZMod p) k]
      LinearContinuousClass k Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k) :=
  linearCoefficientClass (rootCoefficientExtension (K := K) hζ k)
    (rootCoefficientExtension_equivariant hζ k)

variable [IsGalois K L]
    (roots : ∀ q : Kˣ, ∃ b : Lˣ, b ^ p = Units.map (algebraMap K L) q)
    (A : ValuationSubring K)

/-- The residual-field extension of the prime Kummer unit subspace. -/
noncomputable def extendedUnitSubspace : Submodule k
    (LinearContinuousClass k Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)) :=
  Submodule.span k (extendRootClass hζ k '' (primeUnitSubspace roots A : Set _))

/-- Every prime unit class maps to the extended unit subspace. -/
theorem extendRootClass_mem {x : LinearContinuousClass (ZMod p) Gal(L/K) (RootModule L p)}
    (hx : x ∈ primeUnitSubspace roots A) :
    extendRootClass hζ k x ∈ extendedUnitSubspace hζ k roots A :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- Nonzero residual-field scalar changes preserve and reflect the extended subspace. -/
theorem extendedUnitSubspace_smul_iff (a : kˣ)
    (x : LinearContinuousClass k Gal(L/K)
      (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)) :
    (a : k) • x ∈ extendedUnitSubspace hζ k roots A ↔
      x ∈ extendedUnitSubspace hζ k roots A := by
  constructor
  · intro hx
    have h := (extendedUnitSubspace hζ k roots A).smul_mem (↑a⁻¹ : k) hx
    simpa only [smul_smul, Units.inv_mul, one_smul] using h
  · exact (extendedUnitSubspace hζ k roots A).smul_mem _

/-- The same unit condition on the original continuous splitting quotient. -/
def IsExtendedUnitClass (x : ContinuousClass Gal(L/K)
    (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)) : Prop :=
  (linearClassEquiv (k := k)).symm x ∈ extendedUnitSubspace hζ k roots A

/-- Actual coefficient scaling on the original quotient preserves and reflects unit membership. -/
theorem isExtendedUnitClass_scalar_iff (a : kˣ)
    (x : ContinuousClass Gal(L/K) (CharacterModule (primeCyclotomicCharacter (K := K) hζ) k)) :
    IsExtendedUnitClass hζ k roots A
      (mapCoefficientClass (scalarCoefficientEquiv a) (scalarCoefficientEquiv_equivariant a) x) ↔
        IsExtendedUnitClass hζ k roots A x := by
  obtain ⟨y, rfl⟩ := (linearClassEquiv (k := k)).surjective x
  rw [← linearClassEquiv_smul]
  simp only [IsExtendedUnitClass, Equiv.symm_apply_apply]
  exact extendedUnitSubspace_smul_iff hζ k roots A a y

end KummerTheory
