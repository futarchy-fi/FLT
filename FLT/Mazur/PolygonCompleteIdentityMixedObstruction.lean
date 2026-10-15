/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentIdentityIdeal
public import FLT.Mazur.PolygonCompleteIdentityObstructionNormalization

/-!
# The uniquely determined mixed part of the original multiplication obstruction

The two proved unit laws remove the two identity factors. The remaining
Laurent polynomial is uniquely determined and detects the original next-order law.
No vanishing of this mixed polynomial is asserted.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentIdentityIdeal
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "O" => completeIdentityFiniteMulObstruction K n h i m
local notation "D" => (C (T 1 - 1) * (T 1 - 1) : K[T;T⁻¹][T;T⁻¹])

/-- Both identity factors divide the actual reduced next-order obstruction. -/
theorem completeIdentityFiniteMulObstruction_identity_dvd
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) : (D) ∣ (O) :=
  (bothUnits_eq_zero_iff (O)).mp
    ⟨completeIdentityFiniteMulObstruction_firstUnit K n h i m hm,
      completeIdentityFiniteMulObstruction_secondUnit K n h i m hm⟩

/-- The product of the two identity equations is nonzero over the original reduced field. -/
theorem completeIdentityMixedFactor_ne_zero : (D) ≠ 0 := by
  apply mul_ne_zero _ coordinate_sub_one_ne_zero
  intro he
  have hc := congrArg (fun p : K[T;T⁻¹][T;T⁻¹] ↦ p.coeff 0) he
  exact coordinate_sub_one_ne_zero (by simpa using hc)

/-- Extract the actual mixed quotient when the two identity factors divide the obstruction. -/
def completeIdentityMixedObstruction : K[T;T⁻¹][T;T⁻¹] := by
  classical
  exact if hd : (D) ∣ (O) then Classical.choose hd else 0
local notation "M" => completeIdentityMixedObstruction K n h i m

/-- The mixed quotient reconstructs the entire original obstruction, not just its support. -/
theorem completeIdentityMixedObstruction_factor
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) : (O) = (D) * (M) := by
  have hd := completeIdentityFiniteMulObstruction_identity_dvd K n h i m hm
  rw [completeIdentityMixedObstruction, dite_eq_left hd]
  exact Classical.choose_spec hd

/-- No choice remains in the mixed polynomial once its original obstruction is fixed. -/
theorem completeIdentityMixedObstruction_unique
    (hm : completeIdentityFiniteMulDefect K n h i m = 0)
    (q : K[T;T⁻¹][T;T⁻¹]) (hq : (O) = (D) * q) : q = (M) := by
  apply mul_left_cancel₀ (completeIdentityMixedFactor_ne_zero K)
  exact hq.symm.trans (completeIdentityMixedObstruction_factor K n h i m hm)

/-- The mixed polynomial detects the full next original multiplication law. -/
theorem completeIdentityFiniteMulDefect_succ_iff_mixed
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) :
    completeIdentityFiniteMulDefect K n h i (m + 1) = 0 ↔ (M) = 0 := by
  rw [completeIdentityFiniteMulDefect_succ_iff K n h i m hm,
    completeIdentityMixedObstruction_factor K n h i m hm, mul_eq_zero]
  exact or_iff_right (completeIdentityMixedFactor_ne_zero K)

/-- The first still-open law is exactly vanishing of this actual mixed polynomial over K. -/
theorem completeIdentityFiniteMulObstruction_zero_iff_mixed :
    completeIdentityFiniteMulObstruction K n h i 0 = 0 ↔
      completeIdentityMixedObstruction K n h i 0 = 0 := by
  rw [completeIdentityMixedObstruction_factor K n h i 0
    (completeIdentityFiniteMulDefect_zero K n h i), mul_eq_zero]
  exact or_iff_right (completeIdentityMixedFactor_ne_zero K)

end FLT.Mazur.PolygonInfinitesimalStages
