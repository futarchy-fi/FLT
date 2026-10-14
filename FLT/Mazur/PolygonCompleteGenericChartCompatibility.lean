/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericChartOperations

/-!
# Chart operations agree on arbitrary generic test schemes

These are equalities of actual relative scheme morphisms. The hypotheses
only identify two chart presentations of the same inputs; the output
compatibility follows from the constructed generic group and its projections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupObjectPointTranslation GroupSchemePointAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation translation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
variable {T : Over (Spec (.of L))}
local notation "e" => pointsEquiv s (completePointOriginalBaseGroup K n h (0 : Fin n)) T

include ha hs

/-- Changing both chart presentations leaves their actual generic product unchanged. -/
theorem completeGenericChartMul_compatible (b c d e' : ZMod n)
    (x x' y y' : (Over.map s).obj T ⟶ (G).X)
    (hx : x ≫ completeIdentityChart K n h 0 b = x' ≫ completeIdentityChart K n h 0 d)
    (hy : y ≫ completeIdentityChart K n h 0 c = y' ≫ completeIdentityChart K n h 0 e') :
    lift x y ≫ completeIdentityChartMul K n h 0 b c =
      lift x' y' ≫ completeIdentityChartMul K n h 0 d e' := by
  have hx' := (completeGenericChart_eq_iff K n h L a ha p q hs b d ((e) x) ((e) x')).mp
    (by simpa only [MulEquiv.symm_apply_apply] using hx)
  have hy' := (completeGenericChart_eq_iff K n h L a ha p q hs c e' ((e) y) ((e) y')).mp
    (by simpa only [MulEquiv.symm_apply_apply] using hy)
  have h₁ := completeGenericChartMul_evaluation K n h L a ha p q hs b c ((e) x) ((e) y)
  have h₂ := completeGenericChartMul_evaluation K n h L a ha p q hs d e' ((e) x') ((e) y')
  simp only [MulEquiv.symm_apply_apply] at h₁ h₂
  apply Over.OverMorphism.ext
  apply (cancel_mono (π).smoothLocus.ι).mp
  rw [h₁, h₂, hx', hy']

/-- Changing chart presentation leaves actual generic inversion unchanged. -/
theorem completeGenericChartInv_compatible (b c : ZMod n)
    (x y : (Over.map s).obj T ⟶ (G).X)
    (he : x ≫ completeIdentityChart K n h 0 b = y ≫ completeIdentityChart K n h 0 c) :
    x ≫ completeIdentityChartInv K n h 0 b = y ≫ completeIdentityChartInv K n h 0 c := by
  have he' := (completeGenericChart_eq_iff K n h L a ha p q hs b c ((e) x) ((e) y)).mp
    (by simpa only [MulEquiv.symm_apply_apply] using he)
  have h₁ := completeGenericChartInv_evaluation K n h L a ha p q hs b ((e) x)
  have h₂ := completeGenericChartInv_evaluation K n h L a ha p q hs c ((e) y)
  simp only [MulEquiv.symm_apply_apply] at h₁ h₂
  apply Over.OverMorphism.ext
  apply (cancel_mono (π).smoothLocus.ι).mp
  rw [h₁, h₂, he']

end FLT.Mazur.PolygonInfinitesimalStages
