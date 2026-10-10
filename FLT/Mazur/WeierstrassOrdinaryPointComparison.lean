/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryFieldAddition
public import FLT.Mazur.WeierstrassOrdinaryGlobalDomains

/-!
# The projective comparison preserves addition on ordinary domains

The actual ordinary input morphism is the categorical pairing of the two
classical points. Its global addition is the scheme point of their classical
sum, as follows from the computed output vector.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory
open WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

/-- Compute the comparison directly from any nonsingular affine chart algebra point. -/
theorem projectiveToIntegral_affineAlgHom (a : Coordinate W 2 →ₐ[R] K)
    (h : (W.map (algebraMap R K)).toAffine.Nonsingular (a (coord W 2 0)) (a (coord W 2 1))) :
    (projectiveToIntegral W (Point.fromAffine (.some _ _ h))).left =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2 := by
  have he : (⟦fun i => a (coord W 2 i)⟧ : PointClass K) =
      (Point.fromAffine (.some _ _ h)).point := by
    apply congrArg (fun v : Fin 3 → K => (⟦v⟧ : PointClass K))
    funext i
    fin_cases i <;> simp
  rw [projectiveToIntegral_chart W _ 2 _ (chartAlgHom_equation W 2 a) (by simp) he,
    integralChartPoint, evaluation_chartAlgHom]

variable (b : Bool) (f : additionChartRing W (ordinaryIndex b) →ₐ[R] K)
  (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (ordinaryInputLeft W b (coord W 2 0))) (f (ordinaryInputLeft W b (coord W 2 1))))
  (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
    (f (ordinaryInputRight W b (coord W 2 0))) (f (ordinaryInputRight W b (coord W 2 1))))

/-- The original ordinary chart point pairs precisely the two classical input points. -/
theorem ordinaryFieldPoint_pair :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ordinaryGlobalDomain W b =
      (lift (projectiveToIntegral W (Point.fromAffine (.some _ _ h₁)))
        (projectiveToIntegral W (Point.fromAffine (.some _ _ h₂)))).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, ordinaryGlobalDomain_fst, ← Category.assoc, ← Spec.map_comp]
    rw [Over.lift_left]
    exact (projectiveToIntegral_affineAlgHom W (f.comp (ordinaryInputLeft W b)) h₁).symm.trans
      (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, ordinaryGlobalDomain_snd, ← Category.assoc, ← Spec.map_comp]
    rw [Over.lift_left]
    exact (projectiveToIntegral_affineAlgHom W (f.comp (ordinaryInputRight W b)) h₂).symm.trans
      (pullback.lift_snd _ _ _).symm

/-- The actual ordinary-domain sum equals the scheme point of the classical sum. -/
theorem projectiveToIntegral_add_ordinary (hΔ : IsUnit W.Δ) :
    projectiveToIntegral W (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂)) =
      lift (projectiveToIntegral W (Point.fromAffine (.some _ _ h₁)))
        (projectiveToIntegral W (Point.fromAffine (.some _ _ h₂))) ≫
          integralCurveOverAddition W hΔ := by
  apply Over.OverMorphism.ext
  change _ = (lift (projectiveToIntegral W (Point.fromAffine (.some _ _ h₁)))
    (projectiveToIntegral W (Point.fromAffine (.some _ _ h₂)))).left ≫
      integralCurveAddition W hΔ
  rw [← ordinaryFieldPoint_pair W b f h₁ h₂, Category.assoc,
    ordinaryGlobalDomain_addition, ← Category.assoc, ← Spec.map_comp]
  rw [projectiveToIntegral_chart W _ 2 _
    (chartAlgHom_equation W 2 (f.comp (ordinaryChartAddition W b))) (by simp)
    (ordinarySpecialization_projective_sum W b f h₁ h₂).symm,
    integralChartPoint, evaluation_chartAlgHom]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
