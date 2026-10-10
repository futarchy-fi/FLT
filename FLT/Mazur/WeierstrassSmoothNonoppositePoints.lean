/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothOrdinaryPointComparison
public import FLT.Mazur.WeierstrassNonoppositeOrdinaryLift

/-!
# Smooth addition of nonopposite field points

The proved ordinary-domain lifting covers every nonopposite affine pair.
Its smooth output is the classical sum without assuming good reduction.
-/

@[expose] public noncomputable section

open WeierstrassCurve WeierstrassCurve.Projective
open CategoryTheory CartesianMonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

/-- The comparison preserves addition for every nonopposite pair of affine algebra points. -/
theorem projectiveToSmoothOver_add_affineAlgHom
    (a c : Coordinate W 2 →ₐ[R] K)
    (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular (a (coord W 2 0)) (a (coord W 2 1)))
    (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular (c (coord W 2 0)) (c (coord W 2 1)))
    (h : ¬(a (coord W 2 0) = c (coord W 2 0) ∧
      a (coord W 2 1) = (W.map (algebraMap R K)).toAffine.negY
        (c (coord W 2 0)) (c (coord W 2 1)))) :
    projectiveToSmoothOver W (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂)) =
      lift (projectiveToSmoothOver W (Point.fromAffine (.some _ _ h₁)))
        (projectiveToSmoothOver W (Point.fromAffine (.some _ _ h₂))) ≫
          integralSmoothOverAddition W := by
  obtain ⟨b, f, ha, hc⟩ := exists_nonopposite_ordinary_lift W a c h
  have hf₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (ordinaryInputLeft W b (coord W 2 0))) (f (ordinaryInputLeft W b (coord W 2 1))) := by
    simpa only [← AlgHom.comp_apply, ha] using h₁
  have hf₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (ordinaryInputRight W b (coord W 2 0))) (f (ordinaryInputRight W b (coord W 2 1))) := by
    simpa only [← AlgHom.comp_apply, hc] using h₂
  simpa only [← AlgHom.comp_apply, ha, hc] using
    projectiveToSmoothOver_add_ordinary W b f hf₁ hf₂

/-- The comparison preserves the sum of any nonopposite classical affine point pair. -/
theorem projectiveToSmoothOver_add_nonopposite {x₁ x₂ y₁ y₂ : K}
    (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular x₂ y₂)
    (h : ¬(x₁ = x₂ ∧ y₁ = (W.map (algebraMap R K)).toAffine.negY x₂ y₂)) :
    projectiveToSmoothOver W (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂)) =
      lift (projectiveToSmoothOver W (Point.fromAffine (.some _ _ h₁)))
        (projectiveToSmoothOver W (Point.fromAffine (.some _ _ h₂))) ≫
          integralSmoothOverAddition W := by
  let a := evaluation W 2 ![x₁, y₁, 1] ((equation_some ..).mpr h₁.left) rfl
  let c := evaluation W 2 ![x₂, y₂, 1] ((equation_some ..).mpr h₂.left) rfl
  have ha (i) : a (coord W 2 i) = ![x₁, y₁, 1] i := evaluation_coord W 2 _ _ _ i
  have hc (i) : c (coord W 2 i) = ![x₂, y₂, 1] i := evaluation_coord W 2 _ _ _ i
  have he := projectiveToSmoothOver_add_affineAlgHom W a c
    (by simpa only [ha, Matrix.cons_val_zero, Matrix.cons_val_one] using h₁)
    (by simpa only [hc, Matrix.cons_val_zero, Matrix.cons_val_one] using h₂)
    (by simpa only [ha, hc, Matrix.cons_val_zero, Matrix.cons_val_one] using h)
  simpa only [ha, hc, Matrix.cons_val_zero, Matrix.cons_val_one] using he

end FLT.Mazur.WeierstrassIntegralChart
