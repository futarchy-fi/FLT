/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPositiveLaw
public import FLT.Mazur.PolygonCompleteIdentityTopLinearization

/-!
# The actual second-order correction after the proved first positive law

The first-stage law supplies the lower-order hypothesis for the next
canonical correction. This gives its normalized coordinate bijection and
an exact criterion for the second original cubic comparison. Vanishing of
the second correction is the remaining node-extension problem.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal LaurentPolynomial
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "q" => completeIdentityTopCorrection K n h 0 1

/-- The proved first positive law kills its entire unchanged Laurent error. -/
theorem completeIdentityFiniteMulDefect_firstPositive :
    completeIdentityFiniteMulDefect K n h 0 1 = 0 :=
  (completeIdentityFiniteLaw_iff_defect K n h 0 1).mp
    (completeIdentityFiniteLaw_firstPositive K n h)

/-- The actual second-order canonical correction is normalized at the identity. -/
theorem completeIdentitySecondCorrection_at_one :
    eval₂ (RingHom.id K) (1 : Kˣ) (q) = 0 :=
  completeIdentityTopCorrection_at_one K n h 0 1
    (completeIdentityFiniteMulDefect_firstPositive K n h)

/-- The exact remaining second original law is detected by its constructed correction. -/
theorem completeIdentityFiniteLaw_second_iff_correction :
    universalEdgeScaling (Ring K 2) ≫ completeIdentityStageTorus K n h 0 2 =
      completeIdentityFiniteOriginalMul K n h 0 2 ↔ (q) = 0 :=
  completeIdentityFiniteLaw_succ_iff_correction K n h 0 1
    (completeIdentityFiniteMulDefect_firstPositive K n h)

/-- The same correction detects the full second-order original cubic comparison. -/
theorem completeIdentityFiniteComparison_second_iff_correction :
    completeIdentityFiniteScaling K n h 2 ≫ completePointToIntegralCubic K n h 0 =
      completeIdentityFiniteInput K n h 0 2 ≫ completeIdentityActionTarget K n h 0 ↔ (q) = 0 := by
  rw [completeIdentityFiniteComparison_iff_laurentLaw,
    completeIdentityFiniteLaw_second_iff_correction]

/-- The constructed next coordinate bijection intertwines actual second-order multiplication. -/
theorem completeIdentitySecondCoordinateEquiv_mul
    (B : Type) [CommRing B] [Algebra (Ring K 2) B] (u v : Bˣ) :
    completeIdentityTopCoordinateEquiv K n h 0 1 B
        (completeIdentityFinitePointMul K n h 0 2 B u v) =
      completeIdentityTopCoordinateEquiv K n h 0 1 B u *
        completeIdentityTopCoordinateEquiv K n h 0 1 B v :=
  completeIdentityTopCoordinateEquiv_mul K n h 0 1 B
    (completeIdentityFiniteMulDefect_firstPositive K n h) u v

end FLT.Mazur.PolygonInfinitesimalStages
