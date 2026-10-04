/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.UnramifiedCharacterSplitting
public import FLT.AbsoluteGaloisGroup.InertiaDescentUniformizer
public import FLT.AbsoluteGaloisGroup.RationalPrimeUniformizer
public import FLT.GroupScheme.RaynaudUnramifiedOrder

/-!
# Integral arithmetic of the unramified character splitting field

The actual character-kernel field has ramification index one. Its integral
closure preserves base uniformizers and all nonzero natural orders. This
constructs the integral splitting base; descent of a twisted group scheme
is a separate obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing IsDiscreteValuationRing GaloisRepresentation.Extensions
namespace LocalRamification
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
variable {k : Type*} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  (χ : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ) (hc : Continuous χ)
  (hχ : localInertiaGroup v ≤ χ.ker)
local notation "N" => characterOpenNormal v χ hc
local notation "L" => openNormalFixedField N
local notation "D" => IntegralClosure O L
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

local instance characterModelFinite : FiniteDimensional Kv L :=
  finiteLevel_finiteDimensional v (characterOpenNormal v χ hc)

local instance characterModelDVR : IsDiscreteValuationRing D :=
  finiteLevel_isDVR v (characterOpenNormal v χ hc)

include hc hχ in
/-- The specified character's integral splitting ring is unramified. -/
theorem finiteCharacter_ramificationIdx_eq_one :
    (IsLocalRing.maximalIdeal D).ramificationIdx O = 1 :=
  ramificationIdx_eq_one_of_inertia_eq_bot v L (finiteCharacter_inertia_eq_bot v χ hc hχ)

/-- The integral closure in that same splitting field is module finite. -/
theorem finiteCharacter_integers_finite : Module.Finite O D := by
  exact IsIntegralClosure.finite O Kv L (integralClosure O L)

include hc hχ in
/-- Every base uniformizer remains a uniformizer in the integral splitting ring. -/
theorem finiteCharacter_uniformizer {π : O} (hπ : Irreducible π) :
    Irreducible (algebraMap O D π) := by
  let : Module.IsTorsionFree O D := by
    rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap Kv L).injective
    exact congrArg Subtype.val hxy
  let : IsDedekindDomain D :=
    IsIntegralClosure.isDedekindDomain O Kv L (integralClosure O L)
  exact irreducible_map_of_ramificationIdx_eq_one hπ
    (finiteCharacter_ramificationIdx_eq_one v χ hc hχ)

include hc hχ in
/-- The nontrivial unramified character extension does not enlarge any base order. -/
theorem finiteCharacter_order_map {a : O} (ha : a ≠ 0) :
    RaynaudParameters.order (algebraMap O D a) = RaynaudParameters.order a := by
  obtain ⟨π, hπ⟩ := exists_irreducible O
  exact RaynaudParameters.order_map_of_uniformizer (algebraMap O D) hπ
    (finiteCharacter_uniformizer v χ hc hχ hπ) ha

include hc hχ in
/-- Any small-ramification inequality on the base persists in the splitting ring. -/
theorem finiteCharacter_order_lt (p : ℕ) (hp : (p : O) ≠ 0)
    (hsmall : RaynaudParameters.order (p : O) < p - 1) :
    RaynaudParameters.order (p : D) < p - 1 := by
  have h := finiteCharacter_order_map v χ hc hχ hp
  rw [map_natCast] at h
  exact h.symm ▸ hsmall

/-- Over the intended rational p-adic base, the small-ramification bound is
proved for every odd prime, including a nontrivial unramified character. -/
theorem finiteCharacter_rational_small_ramification (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (ψ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) →* kˣ)
    (hψc : Continuous ψ) (hψ : localInertiaGroup (LocalCyclotomic.rationalPlace p) ≤ ψ.ker) :
    RaynaudParameters.order (p : IntegralClosure
      ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (openNormalFixedField (characterOpenNormal (LocalCyclotomic.rationalPlace p) ψ hψc))) <
      p - 1 := by
  apply finiteCharacter_order_lt (LocalCyclotomic.rationalPlace p) ψ hψc hψ p
    (LocalCyclotomic.rationalPrime_irreducible p).ne_zero
  rw [RaynaudParameters.order,
    addVal_uniformizer (LocalCyclotomic.rationalPrime_irreducible p)]
  simpa only [ENat.toNat_one] using (show 1 < p - 1 by omega)

end LocalRamification
