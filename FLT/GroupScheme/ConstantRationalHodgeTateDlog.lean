/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantRationalPowerSystem
public import FLT.GroupScheme.RationalPlaceHodgeTateLieTranspose
public import FLT.GroupScheme.RationalPlaceTateRealizationRank
public import FLT.Mathlib.RingTheory.AugmentationUnramifiedCotangent

/-! # The constant system refutes injectivity of the C_p-linear Cartier dlog

The differential has the dual Tate realization as source. For the constant
height-one system its target is zero, while that source has dimension one.
Thus it is the transpose, not this differential, whose injectivity can be a
step in Hodge–Tate comparison.
-/

@[expose] public noncomputable section
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan.ConstantRationalPower
variable (p : ℕ) [Fact p.Prime] (hp : 2 < p)
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- Every original constant level has zero augmentation cotangent. -/
instance levelCotangentSubsingleton (n : ℕ) : Subsingleton (level p n).Cotangent :=
  AlgHom.augmentationCotangent_subsingleton_of_unramified
    (Bialgebra.counitAlgHom O (level p n).CoordinateRing)

/-- The inverse limit of these actual integral cotangents is zero. -/
instance cotangentLimitSubsingleton : Subsingleton (system p hp).cotangentLimit := by
  constructor
  intro x y
  apply (system p hp).cotangentLimit_ext
  intro n
  exact @Subsingleton.elim (level p n).Cotangent (levelCotangentSubsingleton p n) _ _

/-- The original C_p-linear differential of the constant system is identically zero. -/
theorem hodgeTateDlogLinear_eq_zero :
    rationalPlaceHodgeTateDlogLinear (system p hp) = 0 := by
  exact Subsingleton.elim _ _

/-- Its source is the actual dual Tate realization and has dimension one. -/
theorem hodgeTateDlogLinear_source_finrank :
    Module.finrank ℂ_[p] (RationalPlaceTateRealization (system p hp).cartierDual) = 1 :=
  rationalPlace_cartierTateRealization_finrank (system p hp)

/-- A nonzero original Tate realization cannot inject into this zero differential target. -/
theorem hodgeTateDlogLinear_not_injective :
    ¬ Function.Injective (rationalPlaceHodgeTateDlogLinear (system p hp)) := by
  intro h
  let := h.subsingleton
  let : Module.Free ℂ_[p] (RationalPlaceTateRealization (system p hp).cartierDual) :=
    Module.Free.of_subsingleton _ _
  have hz := Module.finrank_eq_zero_of_subsingleton ℂ_[p]
    (RationalPlaceTateRealization (system p hp).cartierDual)
  rw [hodgeTateDlogLinear_source_finrank] at hz
  exact Nat.one_ne_zero hz

/-- All of the original dual Tate realization lies in the differential kernel. -/
theorem hodgeTateDlogLinear_ker_eq_top :
    LinearMap.ker (rationalPlaceHodgeTateDlogLinear (system p hp)) = ⊤ := by
  rw [hodgeTateDlogLinear_eq_zero, LinearMap.ker_zero]

end ThreeAdicPlan.ConstantRationalPower
