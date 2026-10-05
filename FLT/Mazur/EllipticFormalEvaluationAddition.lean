/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalEvaluationCongruence
public import FLT.Mazur.EllipticFormalEvaluationPoint
public import FLT.Mazur.EllipticFormalTangent
public import FLT.Mazur.EllipticFormalMultiplication

/-!
# Evaluation preserves the elliptic formal group operations

Every ring map from formal series to a field preserves the constructed addition,
including coincident evaluated inputs. It consequently preserves multiplication
by natural numbers. This includes convergent evaluation, which is not injective.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {σ : Type*} {K : Type*} [Field K]
variable (W : WeierstrassCurve R) (f : MvPowerSeries σ R →+* K)

/-- Evaluated normalized points are equal exactly when their parameters are equal. -/
theorem evaluationPoint_eq_iff {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    evaluationPoint W f t ht = evaluationPoint W f v hv ↔ f t = f v := by
  refine ⟨evaluationPoint_parameter W f ht hv, fun h => ?_⟩
  apply Point.ext
  change (⟦f ∘ representative W t⟧ : PointClass K) = ⟦f ∘ representative W v⟧
  have hc := evaluation_coordinate_congr W f ht hv h
  simp only [representative, comp_fin3, h, hc]

/-- The tangent identity survives arbitrary evaluation to a field. -/
theorem evaluationPoint_double {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    evaluationPoint W f (add W t t) (constantCoeff_add W ht ht) =
      evaluationPoint W f t ht + evaluationPoint W f t ht := by
  have he := congrArg (fun p : Fin 3 → MvPowerSeries σ R => f ∘ p)
    (dblXYZ_representative W ht)
  rw [← map_dblXYZ, comp_smul] at he
  apply Point.ext
  change (⟦f ∘ representative W (add W t t)⟧ : PointClass K) =
    ((curve W).map f).toProjective.addMap ⟦f ∘ representative W t⟧ ⟦f ∘ representative W t⟧
  rw [addMap_eq, WeierstrassCurve.Projective.add_self, he,
    smul_eq _ ((isUnit_doublingScale W ht).map f)]

/-- Evaluation preserves formal addition, with no distinctness or injectivity condition. -/
theorem evaluationPoint_add {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    evaluationPoint W f (add W t v) (constantCoeff_add W ht hv) =
      evaluationPoint W f t ht + evaluationPoint W f v hv := by
  by_cases he : f t = f v
  · have hp := (evaluationPoint_eq_iff W f ht hv).mpr he
    have hs := (evaluationPoint_eq_iff W f (constantCoeff_add W ht hv)
      (constantCoeff_add W ht ht)).mpr (evaluation_add_congr W f ht hv ht ht rfl he.symm)
    rw [hs, ← hp, evaluationPoint_double W f ht]
  · exact evaluationPoint_add_of_ne W f ht hv he

/-- The zero parameter evaluates to the identity point. -/
@[simp] theorem evaluationPoint_zero : evaluationPoint W f 0 (by simp) = 0 := by
  have he : f ∘ representative W 0 = (-1 : K) • ![0, 1, 0] := by
    simp [representative, coordinate_zero, comp_fin3]
  apply Point.ext
  change (⟦f ∘ representative W 0⟧ : PointClass K) = ⟦![0, 1, 0]⟧
  rw [he, smul_eq _ isUnit_one.neg]

/-- Evaluation intertwines natural formal multiplication and actual scalar multiplication. -/
theorem evaluationPoint_multiply (n : ℕ) {t : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) :
    evaluationPoint W f (multiply W n t) (constantCoeff_multiply W n ht) =
      n • evaluationPoint W f t ht := by
  induction n with
  | zero => simp [multiply]
  | succ n ih =>
    simp only [multiply, evaluationPoint_add W f (constantCoeff_multiply W n ht) ht,
      ih, succ_nsmul]

end FLT.Mazur.FormalInfinity
