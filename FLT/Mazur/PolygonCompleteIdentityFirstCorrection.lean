/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentCocycleCoefficientRecovery
public import FLT.Mazur.PolygonCompleteIdentityObstructionCocycle
public import FLT.Mazur.PolygonCompleteIdentityObstructionNormalization

/-!
# A canonical one-variable correction for the original first error

The actual reduced obstruction is the coboundary of its outer coefficient at
exponent one. Consequently the original first-order law is equivalent to the
vanishing of a single explicitly extracted Laurent polynomial. The correction
is normalized at the identity; its vanishing is not asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentPairNaturality LaurentCocycleCoefficientRecovery
open PolygonChartScaling LaurentCoefficientEvaluation PolygonInfinitesimal
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "O" => completeIdentityFiniteMulObstruction K n h i 0

/-- The actual coefficient giving the canonical first-order change of Laurent coordinate. -/
def completeIdentityFirstCorrection : K[T;T⁻¹] := (O).coeff 1
local notation "q" => completeIdentityFirstCorrection K n h i

/-- The actual two-variable error is exactly the coboundary of its own canonical coefficient. -/
theorem completeIdentityFirstCorrection_formula {S : Type} [CommRing S]
    (f : K →+* S) (u v : Sˣ) :
    pairEval₂ f u v (O) = u.val * eval₂ f v (q) + v.val * eval₂ f u (q) -
      eval₂ f (u * v) (q) :=
  cocycle_recovery f (O) u v
    (completeIdentityFiniteMulObstruction_zero_cocycle K n h i (C.comp f))

/-- The canonical coordinate correction vanishes at the original identity. -/
theorem completeIdentityFirstCorrection_at_one : eval₂ (RingHom.id K) (1 : Kˣ) (q) = 0 := by
  have he := congrArg (fun p : K[T;T⁻¹] ↦ p.coeff 1)
    (completeIdentityFiniteMulObstruction_firstUnit K n h i 0
      (completeIdentityFiniteMulDefect_zero K n h i))
  change eval₂ (RingHom.id K) (1 : Kˣ) ((O).coeff 1) = 0
  simpa only [coeffMap_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    LaurentUnitPoints.evalUnit, Algebra.algebraMap_self] using he

/-- Vanishing of the whole first obstruction is equivalent to vanishing of this one coefficient. -/
theorem completeIdentityFiniteMulObstruction_zero_iff_correction : (O) = 0 ↔ (q) = 0 := by
  constructor
  · intro he
    simp only [completeIdentityFirstCorrection, he, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply]
  · intro hq
    have he := completeIdentityFirstCorrection_formula K n h i
      ((C : K[T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹]).comp C)
      (Units.map (C : K[T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹]) (coordinateUnit (1 : Kˣ)))
      (coordinateUnit (1 : K[T;T⁻¹]ˣ))
    rw [hq, map_zero, map_zero, map_zero, mul_zero, mul_zero, add_zero, sub_zero] at he
    exact (congrArg (fun F : K[T;T⁻¹][T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹] ↦ F (O))
      (pairEval₂_universal (R := K))).symm.trans he

/-- The full original law at the first positive order is detected by the canonical correction. -/
theorem completeIdentityFiniteLaw_one_iff_correction :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 ↔ (q) = 0 := by
  rw [completeIdentityFiniteLaw_one_iff_obstruction,
    completeIdentityFiniteMulObstruction_zero_iff_correction]

end FLT.Mazur.PolygonInfinitesimalStages
