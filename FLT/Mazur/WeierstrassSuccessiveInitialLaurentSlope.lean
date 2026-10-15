/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentRoot
public import FLT.Mazur.WeierstrassSuccessiveAdjacentLaurentSlope

/-!
# Constructed initial and first successive slopes agree on the original edge

The initial Laurent root is built independently from the original initial
coefficients. Uniqueness proves the full arithmetic comparison for both labels.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
variable {R : Type*} [CommRing R] (π : R) (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "U" => rightIncidenceLaurent π

/-- Actual coefficient division preserves the initial Laurent linear coefficient. -/
theorem initialLaurent_linear :
    U (nodeSlopeLinear W π b3) = laurentSlopeLinear W (π * b3) := by
  simp only [nodeSlopeLinear, laurentSlopeLinear, map_add, map_mul, AlgHom.commutes,
    rightIncidenceLaurent_t, ← LaurentPolynomial.C_eq_algebraMap]
  ring

/-- Actual coefficient division preserves the whole initial Laurent constant side. -/
theorem initialLaurent_constant :
    U (nodeSlopeConstant W s π b4 b6) = laurentSlopeConstant W s (π * b4) (π ^ 2 * b6) := by
  simp only [nodeSlopeConstant, laurentSlopeConstant, map_add, map_mul, map_pow,
    AlgHom.commutes, rightIncidenceLaurent_t, rightIncidenceLaurent_u,
    ← LaurentPolynomial.C_eq_algebraMap]
  ring

variable (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "v₁" => nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "v₀" => nilpotentLaurentSlope W s (π * b3) (π * b4) (π ^ 2 * b6)
  I hI ha hs h2 (I.mul_mem_left π h3) (I.mul_mem_left π h4) (I.mul_mem_left (π ^ 2) h6)

/-- The actual small first-branch slope is the independently constructed initial Laurent root. -/
theorem initialLaurent_nilpotentSlope : U v₁ = v₀ := by
  apply NilpotentQuadraticRoot.root_unique (laurentArithmeticIdeal I)
    (laurentArithmeticIdeal_nilpotent I hI) (laurentSlopeLinear W (π * b3))
    (laurentSlopeConstant W s (π * b4) (π ^ 2 * b6))
    (laurentSlopeLinear_unit W (π * b3) I hI ha (I.mul_mem_left π h3))
  · exact incidenceLaurent_ideal π I U (nilpotentNodeSlope_mem W s π b3 b4 b6
      I hI ha hs h2 h3 h4 h6)
  · exact nilpotentLaurentSlope_mem W s (π * b3) (π * b4) (π ^ 2 * b6)
      I hI ha hs h2 (I.mul_mem_left π h3) (I.mul_mem_left π h4)
      (I.mul_mem_left (π ^ 2) h6)
  · have H := congrArg U (nilpotentNodeSlope_equation W s π b3 b4 b6
      I hI ha hs h2 h3 h4 h6)
    simpa only [map_add, map_mul, map_pow, initialLaurent_linear,
      initialLaurent_constant] using H
  · exact nilpotentLaurentSlope_equation W s (π * b3) (π * b4) (π ^ 2 * b6)
      I hI ha hs h2 (I.mul_mem_left π h3) (I.mul_mem_left π h4)
      (I.mul_mem_left (π ^ 2) h6)

/-- The opposite label also agrees with the original initial Laurent root construction. -/
theorem initialLaurent_oppositeSlope :
    U (oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6) =
      QuadraticRootBranchLocalization.oppositeRoot (laurentSlopeLinear W (π * b3)) v₀ := by
  simp only [oppositeNodeSlope, QuadraticRootBranchLocalization.oppositeRoot, map_sub, map_neg]
  rw [initialLaurent_nilpotentSlope, initialLaurent_linear]

end FLT.Mazur.WeierstrassSuccessiveX
