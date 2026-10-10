/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticProjectiveReduction

/-!
# Normalized integral representatives of the original generic point

A unit coordinate in a primitive lift can be made one by an integral unit.
The resulting vector retains both the original generic class and its actual
projective reduction, including when that reduction is singular.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Every generic point has normalized integral coordinates with its exact reduction. -/
theorem exists_normalized_integral_lift
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    ∃ (j : Fin 3) (v : Fin 3 → A), W.toProjective.Equation v ∧ v j = 1 ∧
      (⟦fun i => (v i : K)⟧ : PointClass K) = P.point ∧
      (⟦residue A ∘ v⟧ : PointClass (ResidueField A)) = projectiveReduction A W P := by
  let w := primitiveLift A W P
  obtain ⟨j, hj⟩ := w.primitive
  let v : Fin 3 → A := hj.unit⁻¹ • w.coords
  have hvj : v j = 1 := by
    change (↑hj.unit⁻¹ : A) * w.coords j = 1
    calc
      _ = (↑hj.unit⁻¹ : A) * ↑hj.unit :=
        congrArg ((↑hj.unit⁻¹ : A) * ·) hj.unit_spec.symm
      _ = 1 := hj.unit.inv_mul
  have he : (⟦fun i => (v i : K)⟧ : PointClass K) = P.point := by
    apply Eq.trans _ w.represents
    apply Quotient.sound
    refine ⟨Units.map (algebraMap A K) hj.unit⁻¹, ?_⟩
    funext i
    exact (map_mul (algebraMap A K) _ _).symm
  let l : PrimitiveLift A P.point := ⟨v, ⟨j, hvj ▸ isUnit_one⟩, he⟩
  exact ⟨j, v, l.equation A W, hvj, he, (projectiveReduction_eq A W P l).symm⟩

end FLT.Mazur
