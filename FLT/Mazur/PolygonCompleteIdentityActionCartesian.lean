/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionTarget
public import FLT.Mazur.PolygonCompletePointSurjective

/-!
# The whole identity-action input is a Cartesian change of the contraction

The comparison with the actual cubic action product is the base change of
the original contraction. In particular every original ideal, including its
nonreduced structure, has exactly the expected pullback on the full input.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "π" => exactVeroneseProjToBase K n h
local notation "e" => completePointSmoothCubicIso K n h i
local notation "q" => completeIdentityActionToCubicProduct K n h i

/-- The input comparison is the full Cartesian change of the original contraction. -/
theorem completeIdentityActionToCubicProduct_isPullback :
    IsPullback (q) (pullback.snd (G).X.hom (π))
      (pullback.snd (integralSmoothStructure (W)) (integralCurveStructure (W))) (g) := by
  have H : IsPullback (pullback.fst (G).X.hom (π) ≫ (e).hom)
      (pullback.snd (G).X.hom (π)) (integralSmoothStructure (W))
      ((g) ≫ integralCurveStructure (W)) := by
    apply (IsPullback.of_hasPullback (G).X.hom (π)).of_iso
      (Iso.refl _) (e) (Iso.refl _) (asIso (S).toSpecΓ)
    · exact (Category.id_comp _).symm
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · exact (completeIdentityActionParameter_structure K n h i).symm
    · simp only [Iso.refl_hom, Category.id_comp]
      exact (completePointToIntegralCubic_over K n h i).symm
  have H' : IsPullback ((q) ≫ pullback.fst _ _) (pullback.snd (G).X.hom (π))
      (integralSmoothStructure (W)) ((g) ≫ integralCurveStructure (W)) := by
    rw [completeIdentityActionToCubicProduct_fst]
    exact H
  exact H'.of_right (completeIdentityActionToCubicProduct_snd K n h i)
    (IsPullback.of_hasPullback (integralSmoothStructure (W)) (integralCurveStructure (W)))

/-- The whole input comparison is proper, including above contracted components. -/
instance completeIdentityActionToCubicProduct_proper : IsProper (q) := by
  let _ := completePointToIntegralCubic_proper K n h i
  exact MorphismProperty.of_isPullback
    (completeIdentityActionToCubicProduct_isPullback K n h i).flip inferInstance

/-- Every smooth-parameter and whole-cubic pair has an original input above it. -/
instance completeIdentityActionToCubicProduct_surjective : Surjective (q) := by
  let _ := completePointToIntegralCubic_surjective K n h i
  exact MorphismProperty.of_isPullback
    (completeIdentityActionToCubicProduct_isPullback K n h i).flip inferInstance

/-- Every original cubic ideal pulls back with its full scheme structure on the whole input. -/
theorem completeIdentityActionToCubicProduct_ideal
    (I : (integralCurve (W)).IdealSheafData) :
    (I.comap (pullback.snd (integralSmoothStructure (W)) (integralCurveStructure (W)))).comap
      (q) = (I.comap (g)).comap (pullback.snd (G).X.hom (π)) := by
  rw [← Scheme.IdealSheafData.comap_comp, completeIdentityActionToCubicProduct_snd,
    Scheme.IdealSheafData.comap_comp]

end FLT.Mazur.PolygonInfinitesimalStages
