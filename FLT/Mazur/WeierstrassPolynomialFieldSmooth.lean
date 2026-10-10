/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveRelativeSmoothCriterion
public import FLT.Mazur.WeierstrassProjectiveAdditionChart

/-!
# Polynomial addition preserves smooth field points

A nonzero homogeneous polynomial output comes from distinct projective inputs,
so the classical nonsingularity theorem for addition applies. Normalizing any
nonzero output coordinate preserves nonsingularity, in every reduction type.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- Every nonzero polynomial addition output of nonsingular points is nonsingular. -/
theorem projectiveAdd_nonsingular_of_coordinate
    (E : WeierstrassCurve K) {P Q : Fin 3 → K}
    (hP : E.toProjective.Nonsingular P) (hQ : E.toProjective.Nonsingular Q)
    (t : Fin 3) (ht : E.toProjective.addXYZ P Q t ≠ 0) :
    E.toProjective.Nonsingular (E.toProjective.addXYZ P Q) := by
  have hn : ¬P ≈ Q := by
    rintro ⟨a, ha⟩
    have he : E.toProjective.addXYZ P Q =
        ((a : K) * 1) ^ 2 • E.toProjective.addXYZ Q Q := by
      rw [← ha]
      simpa only [one_smul, Units.smul_def] using
        (addXYZ_smul (W' := E.toProjective) Q Q (a : K) 1)
    apply ht
    rw [he, addXYZ_self]
    fin_cases t <;> simp
  simpa only [add_of_not_equiv hn] using nonsingular_add hP hQ

variable (W : WeierstrassCurve R) (j k t : Fin 3)
  (f : AdditionOutputOpen W j k t →ₐ[R] K)

/-- The original normalized polynomial chart preserves nonsingularity of both inputs. -/
theorem polynomialFieldPoint_nonsingular
    (hl : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ additionOutputRestriction W j k t ∘ chartProductLeft W j k ∘ coord W j))
    (hr : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ additionOutputRestriction W j k t ∘ chartProductRight W j k ∘ coord W k)) :
    (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ projectiveAdditionChart W j k t ∘ coord W t) := by
  let a := f.comp (additionOutputRestriction W j k t)
  have hu : IsUnit (f (additionOutputInverse W j k t)) :=
    (Units.isUnit _).map f
  have ht : a (chartProductAdditionCoordinates W j k t) ≠ 0 :=
    ((additionOutput_isUnit W j k t).map f).ne_zero
  have he : f ∘ projectiveAdditionChart W j k t ∘ coord W t =
      f (additionOutputInverse W j k t) • (a ∘ chartProductAdditionCoordinates W j k) := by
    funext i
    simp only [Function.comp_apply, projectiveAdditionChart_coord, map_mul,
      Pi.smul_apply, smul_eq_mul, a, AlgHom.comp_apply]
  rw [he, nonsingular_smul _ hu, chartProductAdditionCoordinates_map]
  apply projectiveAdd_nonsingular_of_coordinate _ hl hr t
  have hm := congrFun (chartProductAdditionCoordinates_map W j k a) t
  exact hm ▸ ht

/-- The field-valued polynomial output lands in the actual relative smooth open. -/
theorem polynomialFieldPoint_range_smooth
    (hl : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ additionOutputRestriction W j k t ∘ chartProductLeft W j k ∘ coord W j))
    (hr : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ additionOutputRestriction W j k t ∘ chartProductRight W j k ∘ coord W k)) :
    Set.range (Spec.map (CommRingCat.ofHom
      (f.comp (projectiveAdditionChart W j k t)).toRingHom) ≫ integralCurveChart W t) ⊆
      integralSmoothOpen W :=
  chartFieldPoint_range_smooth W t _ (polynomialFieldPoint_nonsingular W j k t f hl hr)

end FLT.Mazur.WeierstrassIntegralChart
