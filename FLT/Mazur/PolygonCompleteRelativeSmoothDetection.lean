/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFlatSmoothPreimage
public import FLT.Mazur.PolygonCompleteWholeActionRotatedCharts

/-!
# Relative smooth-input detection on the original polygon

A flat relative test scheme detects equality after restricting any chosen
polygon-valued coordinate to the original smooth open.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "π" => exactVeroneseProjToBase K n h
local notation "j" => completeWholeSmoothInclusion K n h

/-- Smooth tests in any polygon coordinate determine maps from a flat relative source. -/
theorem completeRelative_smooth_ext {T Y : Over (Spec (.of (PowerSeries K)))}
    [Flat T.hom] [IsSeparated Y.hom] (p : T ⟶ (X)) (f g : T ⟶ Y)
    (he : ∀ (U : Over (Spec (.of (PowerSeries K)))) (u : U ⟶ T) (y : U ⟶ (M)),
      u ≫ p = y ≫ (j) → u ≫ f = u ≫ g) : f = g := by
  let V := p.left ⁻¹ᵁ (π).smoothLocus
  let U := Over.mk (V.ι ≫ T.hom)
  let u : U ⟶ T := Over.homMk V.ι rfl
  let q : V.toScheme ⟶ (M).left := IsOpenImmersion.lift (π).smoothLocus.ι
    (V.ι ≫ p.left) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨p.left (V.ι x), x.2⟩, rfl⟩)
  have hq : q ≫ (π).smoothLocus.ι = V.ι ≫ p.left :=
    IsOpenImmersion.lift_fac _ _ _
  let y : U ⟶ (M) := Over.homMk q (by
    change q ≫ ((π).smoothLocus.ι ≫ (π)) = V.ι ≫ T.hom
    rw [← Category.assoc, hq, Category.assoc]
    exact congrArg (V.ι ≫ ·) p.w)
  have hp : u ≫ p = y ≫ (j) := by
    apply Over.OverMorphism.ext
    exact hq.symm
  let _ : Flat (p.left ≫ (π)) := by
    change Flat (p.left ≫ (X).hom)
    rw [p.w]
    infer_instance
  apply Over.OverMorphism.ext
  apply completeFlat_smoothPreimage_ext K n h p.left Y.hom f.left g.left
  · exact f.w.trans g.w.symm
  · exact congrArg Over.Hom.left (he U u y hp)

/-- The original full smooth factor is flat over the unchanged base. -/
instance completeOriginalSmoothOver_flat : Flat (M).hom := by
  let _ := exactVeroneseProjToBase_flat K n h
  change Flat ((π).smoothLocus.ι ≫ (π))
  infer_instance

/-- Relative products of flat original-base schemes remain flat. -/
theorem completeRelative_tensor_flat (A B : Over (Spec (.of (PowerSeries K))))
    [Flat A.hom] [Flat B.hom] : Flat (A ⊗ B).hom := by
  change Flat (pullback.fst A.hom B.hom ≫ A.hom)
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
