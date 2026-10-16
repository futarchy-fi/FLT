/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentCocycleCoefficientRecovery
public import FLT.Mazur.PolygonCompleteIdentityTopObstructionCocycle
public import FLT.Mazur.PolygonCompleteIdentityObstructionNormalization

/-!
# Canonical corrections for every successive original multiplication law

The next reduced obstruction is the coboundary of its own coefficient at
exponent one whenever the preceding original law holds. This constructs
its canonical normalized correction and detects exact next-order equality.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentPairNaturality LaurentCocycleCoefficientRecovery
open PolygonChartScaling LaurentCoefficientEvaluation PolygonInfinitesimal
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "O" => completeIdentityFiniteMulObstruction K n h i m

/-- The actual coefficient giving the canonical next-order change of Laurent coordinate. -/
def completeIdentityTopCorrection : K[T;T⁻¹] := (O).coeff 1
local notation "q" => completeIdentityTopCorrection K n h i m

/-- The actual two-variable error is exactly the coboundary of its own canonical coefficient. -/
theorem completeIdentityTopCorrection_formula
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) {S : Type} [CommRing S]
    (f : K →+* S) (u v : Sˣ) :
    pairEval₂ f u v (O) = u.val * eval₂ f v (q) + v.val * eval₂ f u (q) -
      eval₂ f (u * v) (q) :=
  cocycle_recovery f (O) u v
    (completeIdentityFiniteMulObstruction_top_cocycle K n h i m hm (C.comp f))

/-- The canonical coordinate correction vanishes at the original identity. -/
theorem completeIdentityTopCorrection_at_one
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) :
    eval₂ (RingHom.id K) (1 : Kˣ) (q) = 0 := by
  have he := congrArg (fun p : K[T;T⁻¹] ↦ p.coeff 1)
    (completeIdentityFiniteMulObstruction_firstUnit K n h i m hm)
  change eval₂ (RingHom.id K) (1 : Kˣ) ((O).coeff 1) = 0
  simpa only [coeffMap_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    LaurentUnitPoints.evalUnit, Algebra.algebraMap_self] using he

/-- Vanishing of the whole next obstruction is equivalent to vanishing of this one coefficient. -/
theorem completeIdentityFiniteMulObstruction_top_iff_correction
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) : (O) = 0 ↔ (q) = 0 := by
  constructor
  · intro he
    simp only [completeIdentityTopCorrection, he, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply]
  · intro hq
    have he := completeIdentityTopCorrection_formula K n h i m hm
      ((C : K[T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹]).comp C)
      (Units.map (C : K[T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹]) (coordinateUnit (1 : Kˣ)))
      (coordinateUnit (1 : K[T;T⁻¹]ˣ))
    rw [hq, map_zero, map_zero, map_zero, mul_zero, mul_zero, add_zero, sub_zero] at he
    exact (congrArg (fun F : K[T;T⁻¹][T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹] ↦ F (O))
      (pairEval₂_universal (R := K))).symm.trans he

/-- The full original law at the next positive order is detected by the canonical correction. -/
theorem completeIdentityFiniteLaw_succ_iff_correction
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) :
    universalEdgeScaling (Ring K (m + 1)) ≫ completeIdentityStageTorus K n h i (m + 1) =
      completeIdentityFiniteOriginalMul K n h i (m + 1) ↔ (q) = 0 := by
  rw [completeIdentityFiniteLaw_iff_defect,
    completeIdentityFiniteMulDefect_succ_iff K n h i m hm,
    completeIdentityFiniteMulObstruction_top_iff_correction K n h i m hm]

end FLT.Mazur.PolygonInfinitesimalStages
