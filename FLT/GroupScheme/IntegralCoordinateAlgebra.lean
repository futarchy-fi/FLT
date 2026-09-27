/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModel
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Integral closures of generic coordinate algebras

The integral closure gives the candidate integral coordinate algebra. Finiteness and
the generic-fibre comparison do not require an unramifiedness hypothesis.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace ThreeAdicPlan

section IntegralClosure

variable (R K A : Type) [CommRing R] [IsDomain R] [Field K] [CommRing A]
  [Algebra R K] [IsFractionRing R K] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A]

/-- The integral closure in a finite reduced algebra over a perfect fraction field
is finite, including when that algebra is a product of fields. -/
theorem integralClosureFinite [IsIntegrallyClosed R] [IsNoetherianRing R]
    [PerfectField K] [Module.Finite K A] [IsReduced A] :
    Module.Finite R (integralClosure R A) := by
  let : IsArtinianRing A := .of_finite K A
  let F (m : MaximalSpectrum A) := A ⧸ m.asIdeal
  let (m : MaximalSpectrum A) : Field (F m) := Ideal.Quotient.field m.asIdeal
  let (m : MaximalSpectrum A) : Module.Finite R (integralClosure R (F m)) :=
    IsIntegralClosure.finite R K (F m) (integralClosure R (F m))
  let e : A ≃ₐ[R] ∀ m : MaximalSpectrum A, F m :=
    (IsArtinianRing.equivPi A).restrictScalars R
  let f : integralClosure R A →ₐ[R] ∀ m : MaximalSpectrum A, integralClosure R (F m) :=
    AlgHom.pi fun m ↦ ((Pi.evalAlgHom R F m).comp e.toAlgHom).mapIntegralClosure
  exact Module.Finite.of_injective f.toLinearMap (by
    intro x y h
    apply Subtype.ext
    apply e.injective
    funext m
    exact congrArg (fun z ↦ (z m : F m)) h)

/-- Extending the inclusion of the integral closure to the fraction field. -/
def integralClosureGenericMap : K ⊗[R] integralClosure R A →ₐ[K] A :=
  AlgHom.liftEquiv R K (integralClosure R A) A (integralClosure R A).val

omit [IsDomain R] [IsFractionRing R K] in
/-- The generic-fibre map sends a pure tensor to scalar multiplication. -/
@[simp] theorem integralClosureGenericMap_tmul (k : K) (a : integralClosure R A) :
    integralClosureGenericMap R K A (k ⊗ₜ[R] a) = k • (a : A) := rfl

omit [IsDomain R] in
/-- The generic-fibre map for an integral closure is injective. -/
theorem integralClosureGenericMap_injective :
    Function.Injective (integralClosureGenericMap R K A) := by
  let : Module.Flat R K := IsLocalization.flat K R⁰
  have hi := Module.Flat.lTensor_preserves_injective_linearMap (M := K)
    (integralClosure R A).val.toLinearMap Subtype.val_injective
  have he : (integralClosureGenericMap R K A).toLinearMap.restrictScalars R =
      ((IsLocalization.moduleLid R⁰ K A).toLinearMap.restrictScalars R).comp
        ((integralClosure R A).val.toLinearMap.lTensor K) := by
    ext k a
    rfl
  change Function.Injective ((integralClosureGenericMap R K A).toLinearMap.restrictScalars R)
  rw [he]
  exact (IsLocalization.moduleLid R⁰ K A).injective.comp hi

/-- Clearing denominators makes every element of an algebraic generic algebra integral. -/
theorem integralClosureGenericMap_surjective [Algebra.IsIntegral K A] :
    Function.Surjective (integralClosureGenericMap R K A) := by
  intro a
  obtain ⟨s, hs⟩ := IsIntegral.exists_multiple_integral_of_isLocalization R⁰ a
    (Algebra.IsIntegral.isIntegral (R := K) a)
  refine ⟨(algebraMap R K s)⁻¹ ⊗ₜ[R] ⟨s • a, hs⟩, ?_⟩
  change (algebraMap R K (s : R))⁻¹ • ((s : R) • a) = a
  rw [← IsScalarTower.algebraMap_smul K (s : R) a,
    smul_smul, inv_mul_cancel₀, one_smul]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property

/-- The integral closure recovers the entire algebraic generic algebra after base change. -/
def integralClosureGenericEquiv [Algebra.IsIntegral K A] :
    K ⊗[R] integralClosure R A ≃ₐ[K] A :=
  AlgEquiv.ofBijective (integralClosureGenericMap R K A)
    ⟨integralClosureGenericMap_injective R K A, integralClosureGenericMap_surjective R K A⟩

omit [IsDomain R] in
include K in
/-- The integral closure is flat over a Dedekind base because it is torsion-free. -/
theorem integralClosureFlat [IsDedekindDomain R] :
    Module.Flat R (integralClosure R A) := by
  let : Module.IsTorsionFree R A := Module.IsTorsionFree.trans_faithfulSMul R K A
  let : Module.IsTorsionFree R (integralClosure R A) :=
    Function.Injective.moduleIsTorsionFree Subtype.val Subtype.val_injective (fun _ _ ↦ rfl)
  infer_instance

/-- A generic counit takes integral elements into the integrally closed base ring. -/
def integralClosureCounit [IsIntegrallyClosed R] (ε : A →ₐ[K] K) :
    integralClosure R A →ₐ[R] R :=
  (IsIntegralClosure.equiv R (integralClosure R K) K R).toAlgHom.comp
    (ε.restrictScalars R).mapIntegralClosure

omit [IsDomain R] in
/-- The integral counit is the restriction of the generic counit. -/
@[simp] theorem algebraMap_integralClosureCounit [IsIntegrallyClosed R]
    (ε : A →ₐ[K] K) (a : integralClosure R A) :
    algebraMap R K (integralClosureCounit R K A ε a) = ε (a : A) :=
  IsIntegralClosure.algebraMap_equiv R (integralClosure R K) K R _

end IntegralClosure

/-- The localization `ℤ[1/S]` for a finite set of natural primes. -/
abbrev ZInvPrimes (S : Finset ℕ) := Localization.Away (∏ p ∈ S, (p : ℤ))

namespace ZInvPrimes

variable (S : Finset ℕ) [Fact (∀ p ∈ S, p.Prime)]

/-- The denominator being inverted is nonzero. -/
theorem denominator_ne_zero : (∏ p ∈ S, (p : ℤ)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact_mod_cast (Fact.out (p := ∀ p ∈ S, p.Prime) p hp).ne_zero

/-- The canonical map from the ring of `S`-integers to the rationals. -/
def toRat : ZInvPrimes S →+* ℚ :=
  IsLocalization.Away.lift (∏ p ∈ S, (p : ℤ))
    (show IsUnit (algebraMap ℤ ℚ (∏ p ∈ S, (p : ℤ))) from
      IsUnit.mk0 _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ ℚ)).mpr
        (denominator_ne_zero S)))

instance : Algebra (ZInvPrimes S) ℚ := (toRat S).toAlgebra

instance : IsDomain (ZInvPrimes S) := Localization.Away.isDomain (denominator_ne_zero S)

section

attribute [local instance 100000] Algebra.toSMul

instance : IsScalarTower ℤ (ZInvPrimes S) ℚ := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (IsLocalization.Away.lift_eq (∏ p ∈ S, (p : ℤ))
    (show IsUnit (algebraMap ℤ ℚ (∏ p ∈ S, (p : ℤ))) from
      IsUnit.mk0 _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ ℚ)).mpr
        (denominator_ne_zero S))) x).symm

instance : IsFractionRing (ZInvPrimes S) ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (∏ p ∈ S, (p : ℤ))) (ZInvPrimes S) ℚ

end

instance : IsDedekindDomain (ZInvPrimes S) :=
  IsLocalization.isDedekindDomain ℤ
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr (denominator_ne_zero S))) _

end ZInvPrimes

namespace FiniteContinuousGaloisModule

attribute [local instance 100000] Algebra.toSMul

variable (S : Finset ℕ) [Fact (∀ p ∈ S, p.Prime)] (W : FiniteContinuousGaloisModule)

instance genericCoordinateAlgebraAlgebra : Algebra (ZInvPrimes S) W.GenericCoordinateAlgebra :=
  Algebra.compHom W.GenericCoordinateAlgebra (algebraMap (ZInvPrimes S) ℚ)

instance genericCoordinateAlgebraScalarTower :
    IsScalarTower (ZInvPrimes S) ℚ W.GenericCoordinateAlgebra :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical candidate integral coordinate algebra, without an étaleness assertion. -/
abbrev IntegralCoordinateAlgebra := integralClosure (ZInvPrimes S) W.GenericCoordinateAlgebra

instance integralCoordinateAlgebraFinite : Module.Finite (ZInvPrimes S)
    (W.IntegralCoordinateAlgebra S) := by
  let : IsReduced W.GenericCoordinateAlgebra :=
    Algebra.FormallyUnramified.isReduced_of_field ℚ W.GenericCoordinateAlgebra
  exact integralClosureFinite (ZInvPrimes S) ℚ W.GenericCoordinateAlgebra

instance integralCoordinateAlgebraFlat : Module.Flat (ZInvPrimes S)
    (W.IntegralCoordinateAlgebra S) :=
  integralClosureFlat (ZInvPrimes S) ℚ W.GenericCoordinateAlgebra

/-- Base change of the candidate integral algebra recovers the generic coordinate algebra. -/
def integralGenericEquiv :
    ℚ ⊗[ZInvPrimes S] W.IntegralCoordinateAlgebra S ≃ₐ[ℚ] W.GenericCoordinateAlgebra :=
  integralClosureGenericEquiv (ZInvPrimes S) ℚ W.GenericCoordinateAlgebra

/-- The comparison is induced by the actual inclusion of integral coordinates. -/
@[simp] theorem integralGenericEquiv_tmul (q : ℚ) (a : W.IntegralCoordinateAlgebra S) :
    W.integralGenericEquiv S (q ⊗ₜ[ZInvPrimes S] a) = q • (a : W.GenericCoordinateAlgebra) :=
  rfl

/-- Negation on the group preserves the integral coordinate algebra. -/
def integralAntipode : W.IntegralCoordinateAlgebra S →ₐ[ZInvPrimes S]
    W.IntegralCoordinateAlgebra S :=
  ((GaloisModule.GenericFiber.antipodeAlgHom ℚ (AlgebraicClosure ℚ) W).restrictScalars
    (ZInvPrimes S)).mapIntegralClosure

/-- Evaluating the integral antipode is precomposition with negation. -/
@[simp] theorem integralAntipode_apply (a : W.IntegralCoordinateAlgebra S) (w : W) :
    (W.integralAntipode S a : W.GenericCoordinateAlgebra) w =
      (a : W.GenericCoordinateAlgebra) (-w) :=
  rfl

/-- The descended antipode is an involution. -/
theorem integralAntipode_involutive : Function.Involutive (W.integralAntipode S) := by
  intro a
  apply Subtype.ext
  ext w
  simp

/-- Evaluation at zero descends to the ring of `S`-integers. -/
def integralCounit : W.IntegralCoordinateAlgebra S →ₐ[ZInvPrimes S] ZInvPrimes S :=
  integralClosureCounit (ZInvPrimes S) ℚ W.GenericCoordinateAlgebra
    (GaloisModule.GenericFiber.counitAlgHom ℚ (AlgebraicClosure ℚ) W)

/-- Compatibility of the integral and generic counits. -/
@[simp] theorem algebraMap_integralCounit (a : W.IntegralCoordinateAlgebra S) :
    algebraMap (ZInvPrimes S) ℚ (W.integralCounit S a) =
      GaloisModule.GenericFiber.counitAlgHom ℚ (AlgebraicClosure ℚ) W a :=
  algebraMap_integralClosureCounit (ZInvPrimes S) ℚ W.GenericCoordinateAlgebra _ a

end FiniteContinuousGaloisModule

end ThreeAdicPlan
