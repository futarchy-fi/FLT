/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveLaurentBoundary
public import FLT.Mazur.WeierstrassSuccessiveOppositeNodeChart

/-!
# The constructed slopes agree on the original adjacent Laurent edge

Uniqueness of the small root proves compatibility, rather than assuming it.
The opposite root then follows with the same label and original coefficients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (π : R) (I : Ideal R)

/-- Incidence evaluation carries the original arithmetic ideal into its scalar extension. -/
theorem incidenceLaurent_ideal (f : SuccessiveIncidence.Coordinate π →ₐ[R] R[T;T⁻¹]) :
    nodeArithmeticIdeal π I ≤ (I.map (algebraMap R R[T;T⁻¹])).comap f.toRingHom := by
  rw [nodeArithmeticIdeal, ← Ideal.map_le_iff_le_comap, Ideal.map_map]
  rw [show f.toRingHom.comp (algebraMap R _) = algebraMap R R[T;T⁻¹] from
    RingHom.ext f.commutes]

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "old" => nilpotentNodeSlope W s π (π * b3) (π * b4) (π ^ 2 * b6)
  I hI ha hs h2 (I.mul_mem_left π h3) (I.mul_mem_left π h4) (I.mul_mem_left (π ^ 2) h6)
local notation "next" => nilpotentNodeSlope W (s * π) π b3 b4 b6
  I hI ha (I.mul_mem_right π hs) h2 h3 h4 h6
local notation "L" => inverseLeftIncidenceLaurent π
local notation "U" => rightIncidenceLaurent π

/-- The original small slope is unchanged along the actual inverse-coordinate edge. -/
theorem adjacentLaurent_nilpotentSlope : L old = U next := by
  let J := I.map (algebraMap R R[T;T⁻¹])
  have hJ : IsNilpotent J := by
    obtain ⟨N, hN⟩ := hI
    refine ⟨N, ?_⟩
    rw [← Ideal.map_pow, hN]
    exact Ideal.map_bot
  apply NilpotentQuadraticRoot.root_unique J hJ
    (U (nodeSlopeLinear W π b3)) (U (nodeSlopeConstant W (s * π) π b4 b6))
    ((nodeSlopeLinear_unit W π b3 I hI ha h3).map U)
  · exact incidenceLaurent_ideal π I L (nilpotentNodeSlope_mem W s π
      (π * b3) (π * b4) (π ^ 2 * b6) I hI ha hs h2
      (I.mul_mem_left π h3) (I.mul_mem_left π h4) (I.mul_mem_left (π ^ 2) h6))
  · exact incidenceLaurent_ideal π I U (nilpotentNodeSlope_mem W (s * π) π b3 b4 b6
      I hI ha (I.mul_mem_right π hs) h2 h3 h4 h6)
  · have he := congrArg L (nilpotentNodeSlope_equation W s π
      (π * b3) (π * b4) (π ^ 2 * b6) I hI ha hs h2
      (I.mul_mem_left π h3) (I.mul_mem_left π h4) (I.mul_mem_left (π ^ 2) h6))
    simpa only [map_add, map_mul, map_pow,
      adjacentLaurent_linear, adjacentLaurent_constant] using he
  · simpa only [map_add, map_mul, map_pow] using
      congrArg U (nilpotentNodeSlope_equation W (s * π) π b3 b4 b6
        I hI ha (I.mul_mem_right π hs) h2 h3 h4 h6)

/-- The opposite branch retains its original label under the same edge identification. -/
theorem adjacentLaurent_oppositeSlope :
    L (oppositeNodeSlope W s π (π * b3) (π * b4) (π ^ 2 * b6)
      I hI ha hs h2 (I.mul_mem_left π h3) (I.mul_mem_left π h4)
        (I.mul_mem_left (π ^ 2) h6)) =
    U (oppositeNodeSlope W (s * π) π b3 b4 b6
      I hI ha (I.mul_mem_right π hs) h2 h3 h4 h6) := by
  simp only [oppositeNodeSlope, QuadraticRootBranchLocalization.oppositeRoot, map_sub, map_neg]
  rw [adjacentLaurent_linear, adjacentLaurent_nilpotentSlope]

end FLT.Mazur.WeierstrassSuccessiveX
