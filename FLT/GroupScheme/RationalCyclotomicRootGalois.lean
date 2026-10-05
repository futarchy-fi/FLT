/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalCyclotomicRootBasis
public import FLT.GroupScheme.PDivisibleTateRootGalois
public import FLT.GroupScheme.PDivisibleRationalCartierPeriodGalois
public import FLT.PadicHodgeTheory.ComplexCyclotomicAction

/-! # The original root module has the standard positive cyclotomic action -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- Original Galois conjugation multiplies the prescribed root vector by the positive character. -/
theorem rationalCyclotomicRootVector_galois (σ : PadicGalois p) :
    tateRootGalois ((rationalPlaceGaloisEquiv p).symm σ) (rationalCyclotomicRootVector p) =
      (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val •
        rationalCyclotomicRootVector p := by
  apply tateRoot_ext
  intro n
  rw [map_smul, tateRootValue_smul, rationalCyclotomicRootVector_value]
  apply Additive.toMul.injective
  apply Units.ext
  apply (rationalPlaceComplexMap p).injective
  change rationalPlaceComplexMap p (((rationalPlaceGaloisEquiv p).symm σ)
    (rationalCyclotomicRoot p n)) = rationalPlaceComplexMap p
      (rationalCyclotomicRoot p n ^ _)
  rw [← rationalPlaceComplexMap_galois, MulEquiv.apply_symm_apply,
    map_pow, rationalCyclotomicRoot_map]
  exact congrArg Subtype.val (complexCyclotomicSequence_action p σ n)

/-- The integral cyclotomic coordinates intertwine the whole original Galois action. -/
theorem rationalCyclotomicRootEquiv_galois (σ : PadicGalois p) (a : ℤ_[p]) :
    tateRootGalois ((rationalPlaceGaloisEquiv p).symm σ) (rationalCyclotomicRootEquiv p a) =
      rationalCyclotomicRootEquiv p
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val * a) := by
  change tateRootGalois _ (a • rationalCyclotomicRootVector p) =
    (_ * a) • rationalCyclotomicRootVector p
  rw [map_smul, rationalCyclotomicRootVector_galois, smul_smul, mul_comm]

/-- Every genuine coherent root transforms by the same standard cyclotomic character. -/
theorem rationalTateRootGalois_eq_smul (σ : PadicGalois p)
    (x : TateRootModule (AlgebraicClosure K) p) :
    tateRootGalois ((rationalPlaceGaloisEquiv p).symm σ) x =
      (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val • x := by
  obtain ⟨a, rfl⟩ := (rationalCyclotomicRootEquiv p).surjective x
  rw [rationalCyclotomicRootEquiv_galois, ← map_smul]
  rfl
end ThreeAdicPlan
