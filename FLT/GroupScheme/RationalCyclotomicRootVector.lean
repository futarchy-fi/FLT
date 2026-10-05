/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalCyclotomicRoots
public import FLT.GroupScheme.TateRootModule

/-! # The chosen primitive vector in the original coherent-root module -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- The prescribed complex roots remain primitive in the original algebraic closure. -/
theorem rationalCyclotomicRoot_primitive (n : ℕ) :
    IsPrimitiveRoot (rationalCyclotomicRoot p n) (p ^ n) := by
  apply IsPrimitiveRoot.of_map_of_injective (f := rationalPlaceComplexMap p) _
    (rationalPlaceComplexMap p).injective
  rw [rationalCyclotomicRoot_map]
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mpr (complexCyclotomicSequence_primitive p n)

/-- The actual unit-valued roots retain their exact orders. -/
theorem rationalCyclotomicUnit_primitive (n : ℕ) :
    IsPrimitiveRoot (rationalCyclotomicUnit p n) (p ^ n) :=
  IsPrimitiveRoot.coe_units_iff.mp (rationalCyclotomicRoot_primitive p n)

/-- The chosen roots form a vector of the original root module. -/
def rationalCyclotomicRootVector : TateRootModule (AlgebraicClosure K) p :=
  ⟨fun n ↦ Additive.ofMul ⟨rationalCyclotomicUnit p n, rationalCyclotomicUnit_pow p n⟩,
    fun h ↦ Additive.toMul.injective (Subtype.ext (rationalCyclotomicUnit_transition p h))⟩

/-- The root vector evaluates to the prescribed original unit. -/
theorem rationalCyclotomicRootVector_value (n : ℕ) :
    tateRootValue (AlgebraicClosure K) p n
      (tateRootEval (AlgebraicClosure K) p n (rationalCyclotomicRootVector p)) =
        Additive.ofMul (rationalCyclotomicUnit p n) := rfl

/-- Scalar multiples of the prescribed vector define the integral cyclotomic parametrization. -/
def rationalCyclotomicRootLinear : ℤ_[p] →ₗ[ℤ_[p]] TateRootModule (AlgebraicClosure K) p :=
  (LinearMap.id : ℤ_[p] →ₗ[ℤ_[p]] ℤ_[p]).smulRight (rationalCyclotomicRootVector p)

/-- The prescribed vector generates every finite root group. -/
theorem rationalCyclotomicRootLinear_level_surjective (n : ℕ) :
    Function.Surjective ((tateRootEval (AlgebraicClosure K) p n).comp
      (rationalCyclotomicRootLinear p)) := by
  intro x
  obtain ⟨i, _, hi⟩ := (rationalCyclotomicUnit_primitive p n).eq_pow_of_mem_rootsOfUnity
    x.toMul.property
  refine ⟨(i : ℤ_[p]), ?_⟩
  change tateRootEval (AlgebraicClosure K) p n ((i : ℤ_[p]) • _) = x
  rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  exact Additive.toMul.injective (Subtype.ext hi)

/-- No nonzero p-adic scalar kills the chosen primitive vector. -/
theorem rationalCyclotomicRootLinear_injective :
    Function.Injective (rationalCyclotomicRootLinear p) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have h := congrArg (fun x ↦ tateRootValue (AlgebraicClosure K) p n
    (tateRootEval (AlgebraicClosure K) p n x)) ha
  change tateRootValue (AlgebraicClosure K) p n
    (tateRootEval (AlgebraicClosure K) p n (a • rationalCyclotomicRootVector p)) = 0 at h
  rw [map_smul, tateRootValue_smul, rationalCyclotomicRootVector_value] at h
  have hd := (rationalCyclotomicUnit_primitive p n).dvd_of_pow_eq_one _
    (congrArg Additive.toMul h)
  rw [map_zero]
  apply ZMod.val_injective
  simpa using Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
end ThreeAdicPlan
