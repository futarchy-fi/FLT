/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticIteratedNodeCorrection

/-!
# Quotient squares for arbitrary finite sequences of node corrections

Induction carries the original arithmetic quotient through every changed
smoothing and every full node factor. No fixed-smoothing assumption is used.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R) (m : ℕ)
  (t : Quotient R π (m + 1)) (s : Quotient R π m)
  (hs : restriction R π m t = s) (q : ℕ → Bool → R[T;T⁻¹])
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "T" => iteratedCorrectionSmoothing R π (m + 1) t q
local notation "S" => iteratedCorrectionSmoothing R π m s q

include hs

/-- Every recursively changed smoothing retains the original coefficient quotient. -/
theorem iteratedCorrectionSmoothing_restriction (k : ℕ) :
    restriction R π m (T k) = S k := by
  induction k with
  | zero => exact hs
  | succ k ih => exact twoBranchCorrectionSmoothing_restriction R π m _ _ ih (q k)

/-- The empty composite retains the original restriction. -/
theorem iteratedCorrectionNodeFactor_zero_restriction :
    (ringMap f t s hs).comp
        (iteratedCorrectionNodeFactor R π (m + 1) t q 0).toAlgHom.toRingHom =
      (iteratedCorrectionNodeFactor R π m s q 0).toAlgHom.toRingHom.comp
        (ringMap f (T 0) (S 0)
          (iteratedCorrectionSmoothing_restriction R π m t s hs q 0)) := by
  apply RingHom.ext
  intro x
  exact (congrArg (ringMap f t s hs)
    (DFunLike.congr_fun (iteratedCorrectionNodeFactor_zero R π (m + 1) t q) x)).trans
      (DFunLike.congr_fun (iteratedCorrectionNodeFactor_zero R π m s q)
        (ringMap f t s hs x)).symm

/-- A full successor factor carries forward a proved quotient square. -/
theorem iteratedCorrectionNodeFactor_step_restriction (k : ℕ)
    (ih : (ringMap f t s hs).comp
        (iteratedCorrectionNodeFactor R π (m + 1) t q k).toAlgHom.toRingHom =
      (iteratedCorrectionNodeFactor R π m s q k).toAlgHom.toRingHom.comp
        (ringMap f (T k) (S k)
          (iteratedCorrectionSmoothing_restriction R π m t s hs q k))) :
    (ringMap f t s hs).comp
        (iteratedCorrectionNodeFactor R π (m + 1) t q (k + 1)).toAlgHom.toRingHom =
      (iteratedCorrectionNodeFactor R π m s q (k + 1)).toAlgHom.toRingHom.comp
        (ringMap f (T (k + 1)) (S (k + 1))
          (iteratedCorrectionSmoothing_restriction R π m t s hs q (k + 1))) := by
  rw [iteratedCorrectionNodeFactor_succ, iteratedCorrectionNodeFactor_succ]
  apply RingHom.ext
  intro x
  have h₁ := DFunLike.congr_fun ih
    (twoBranchCorrectionNodeFactor R π (m + 1) (T k) (q k) x)
  have h₂ := DFunLike.congr_fun
    (twoBranchCorrectionNodeFactor_restriction R π m (T k) (S k)
      (iteratedCorrectionSmoothing_restriction R π m t s hs q k) (q k)) x
  exact h₁.trans (congrArg (iteratedCorrectionNodeFactor R π m s q k) h₂)

/-- The entire finite composite of full node corrections commutes with restriction. -/
theorem iteratedCorrectionNodeFactor_restriction (k : ℕ) :
    (ringMap f t s hs).comp
        (iteratedCorrectionNodeFactor R π (m + 1) t q k).toAlgHom.toRingHom =
      (iteratedCorrectionNodeFactor R π m s q k).toAlgHom.toRingHom.comp
        (ringMap f (T k) (S k)
          (iteratedCorrectionSmoothing_restriction R π m t s hs q k)) := by
  induction k with
  | zero => exact iteratedCorrectionNodeFactor_zero_restriction R π m t s hs q
  | succ k ih => exact iteratedCorrectionNodeFactor_step_restriction R π m t s hs q k ih

end FLT.Mazur.PolygonArithmeticStages
