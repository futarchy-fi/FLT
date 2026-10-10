/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRelativeSmoothOpen
public import FLT.Mazur.WeierstrassProjectivePointComparison

/-!
# Classical nonsingular points lie in the actual relative smooth locus

A nonzero free derivative factors each nonsingular field point through a
standard smooth localization. This works for every coefficient equation,
including varying semistable families, without a unit discriminant.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R)

/-- A nonsingular chart point factors through a free derivative localization. -/
theorem chartFieldPoint_range_smooth (j : Fin 3) (f : Coordinate W j →ₐ[R] K)
    (hn : (W.map (algebraMap R K)).toProjective.Nonsingular (f ∘ coord W j)) :
    Set.range (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j) ⊆
      integralSmoothOpen W := by
  obtain ⟨i, hij, hi⟩ := normalized_free_partial_exists _ j _ hn (by simp)
  rw [← chartPartial_map W j i f] at hi
  let g : Localization.Away (chartPartial W j i) →+* K :=
    IsLocalization.Away.lift (chartPartial W j i) (isUnit_iff_ne_zero.mpr hi)
  have hg : Spec.map (CommRingCat.ofHom g) ≫
      PrincipalAffineRefinement.inclusion (chartPartial W j i) =
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
    rw [PrincipalAffineRefinement.inclusion, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext
      (IsLocalization.Away.lift_comp (chartPartial W j i) (isUnit_iff_ne_zero.mpr hi))
  rw [← hg, Category.assoc]
  rintro _ ⟨x, rfl⟩
  exact chartPartial_global_range_smooth W j i hij
    ⟨(Spec.map (CommRingCat.ofHom g)) x, rfl⟩

/-- Every classical nonsingular point lands in the actual relative smooth open. -/
theorem projectiveToIntegral_range_smooth
    (P : (W.map (algebraMap R K)).toProjective.Point) :
    Set.range ((projectiveToIntegral W P).left : Spec (.of K) ⟶ integralCurve W) ⊆
      (integralSmoothOpen W : Set (integralCurve W)) := by
  obtain ⟨j, v, hv, hj, he⟩ := exists_normalized_projective (W.map (algebraMap R K)) P
  have hn : (W.map (algebraMap R K)).toProjective.Nonsingular v := by
    have h := P.nonsingular
    rw [← he] at h
    exact h
  rw [projectiveToIntegral_chart W P j v hv hj he]
  apply chartFieldPoint_range_smooth
  simpa only [Function.comp_def, evaluation_coord] using hn

/-- The original classical point as an actual point of the entire relative smooth locus. -/
def projectiveToSmooth (P : (W.map (algebraMap R K)).toProjective.Point) :
    Spec (.of K) ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι (projectiveToIntegral W P).left
    (by rw [Scheme.Opens.range_ι]; exact projectiveToIntegral_range_smooth W P)

/-- The smooth point retains its original morphism into the cubic. -/
@[reassoc] theorem projectiveToSmooth_inclusion
    (P : (W.map (algebraMap R K)).toProjective.Point) :
    projectiveToSmooth W P ≫ (integralSmoothOpen W).ι = (projectiveToIntegral W P).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The smooth point preserves the coefficient morphism. -/
theorem projectiveToSmooth_structure
    (P : (W.map (algebraMap R K)).toProjective.Point) :
    projectiveToSmooth W P ≫ integralSmoothStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [integralSmoothStructure, ← Category.assoc, projectiveToSmooth_inclusion]
  exact (projectiveToIntegral W P).w

end FLT.Mazur.WeierstrassIntegralChart
