/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericChartCompatibility
public import FLT.Mazur.PolygonCompleteChartOverlapField

/-!
# Compatibility of the original complete smooth chart operations

Different chart labels force an actual Laurent-series base map. The generic
comparison then proves compatibility over every test scheme; equal labels
are handled by cancellation of the original open chart immersions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open PowerSeriesLaurentGenericOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "V" => completeParameterOpen K n h
variable {T : Over (Spec (.of (PowerSeries K)))}

/-- Reinterpret an original coordinate using a proved Laurent-series base factorization. -/
def completeChartFieldCoordinate (v : T.left ⟶ Spec (.of (LaurentSeries K)))
    (hv : v ≫ genericInclusion K = T.hom) (x : T ⟶ (G).X) :
    (Over.map (genericInclusion K)).obj (Over.mk v) ⟶ (G).X :=
  Over.homMk x.left (x.w.trans hv.symm)

/-- A Laurent-series factorization suffices for compatibility of both chart inputs. -/
theorem completeChartMul_compatible_of_field
    (v : T.left ⟶ Spec (.of (LaurentSeries K))) (hv : v ≫ genericInclusion K = T.hom)
    (b c d e : ZMod n) (x x' y y' : T ⟶ (G).X)
    (hx : x ≫ completeIdentityChart K n h 0 b = x' ≫ completeIdentityChart K n h 0 d)
    (hy : y ≫ completeIdentityChart K n h 0 c = y' ≫ completeIdentityChart K n h 0 e) :
    lift x y ≫ completeIdentityChartMul K n h 0 b c =
      lift x' y' ≫ completeIdentityChartMul K n h 0 d e := by
  have he := completeGenericChartMul_compatible K n h (LaurentSeries K)
    (algebraMap (PowerSeries K) (LaurentSeries K)) (parameter_ne_zero K)
    (V).ι (toField K (π)) (isPullback_toField K (π)) b c d e
    (completeChartFieldCoordinate K n h v hv x)
    (completeChartFieldCoordinate K n h v hv x')
    (completeChartFieldCoordinate K n h v hv y)
    (completeChartFieldCoordinate K n h v hv y')
    (by
      apply Over.OverMorphism.ext
      have he := congrArg Over.Hom.left hx
      exact he)
    (by
      apply Over.OverMorphism.ext
      have he := congrArg Over.Hom.left hy
      exact he)
  apply Over.OverMorphism.ext
  have he' := congrArg Over.Hom.left he
  exact he'

/-- A Laurent-series factorization suffices for compatibility of chart inversion. -/
theorem completeChartInv_compatible_of_field
    (v : T.left ⟶ Spec (.of (LaurentSeries K))) (hv : v ≫ genericInclusion K = T.hom)
    (b c : ZMod n) (x y : T ⟶ (G).X)
    (hx : x ≫ completeIdentityChart K n h 0 b = y ≫ completeIdentityChart K n h 0 c) :
    x ≫ completeIdentityChartInv K n h 0 b = y ≫ completeIdentityChartInv K n h 0 c := by
  have he := completeGenericChartInv_compatible K n h (LaurentSeries K)
    (algebraMap (PowerSeries K) (LaurentSeries K)) (parameter_ne_zero K)
    (V).ι (toField K (π)) (isPullback_toField K (π)) b c
    (completeChartFieldCoordinate K n h v hv x)
    (completeChartFieldCoordinate K n h v hv y)
    (by
      apply Over.OverMorphism.ext
      have he := congrArg Over.Hom.left hx
      exact he)
  apply Over.OverMorphism.ext
  have he' := congrArg Over.Hom.left he
  exact he'

/-- Original chart embeddings are monomorphisms over the unchanged base. -/
theorem completeIdentityChart_mono (b : ZMod n) : Mono (completeIdentityChart K n h 0 b) := by
  let _ := completeIdentityChart_isOpenImmersion K n h 0 b
  exact Over.mono_of_mono_left _

/-- Multiplication is compatible with every pair of original chart presentations. -/
theorem completeChartMul_compatible (b c d e : ZMod n) (x x' y y' : T ⟶ (G).X)
    (hx : x ≫ completeIdentityChart K n h 0 b = x' ≫ completeIdentityChart K n h 0 d)
    (hy : y ≫ completeIdentityChart K n h 0 c = y' ≫ completeIdentityChart K n h 0 e) :
    lift x y ≫ completeIdentityChartMul K n h 0 b c =
      lift x' y' ≫ completeIdentityChartMul K n h 0 d e := by
  by_cases hbd : b = d
  · subst d
    by_cases hce : c = e
    · subst e
      let _ := completeIdentityChart_mono K n h b
      let _ := completeIdentityChart_mono K n h c
      have hx' := (cancel_mono (completeIdentityChart K n h 0 b)).mp hx
      have hy' := (cancel_mono (completeIdentityChart K n h 0 c)).mp hy
      rw [hx', hy']
    · exact completeChartMul_compatible_of_field K n h
        (completeChartOverlapToField K n h 0 c e hce y y' hy)
        (completeChartOverlapToField_base K n h 0 c e hce y y' hy) b c b e x x' y y' hx hy
  · exact completeChartMul_compatible_of_field K n h
      (completeChartOverlapToField K n h 0 b d hbd x x' hx)
      (completeChartOverlapToField_base K n h 0 b d hbd x x' hx) b c d e x x' y y' hx hy

/-- Inversion is compatible with every original chart presentation. -/
theorem completeChartInv_compatible (b c : ZMod n) (x y : T ⟶ (G).X)
    (he : x ≫ completeIdentityChart K n h 0 b = y ≫ completeIdentityChart K n h 0 c) :
    x ≫ completeIdentityChartInv K n h 0 b = y ≫ completeIdentityChartInv K n h 0 c := by
  by_cases hbc : b = c
  · subst c
    let _ := completeIdentityChart_mono K n h b
    rw [(cancel_mono (completeIdentityChart K n h 0 b)).mp he]
  · exact completeChartInv_compatible_of_field K n h
      (completeChartOverlapToField K n h 0 b c hbc x y he)
      (completeChartOverlapToField_base K n h 0 b c hbc x y he) b c x y he

end FLT.Mazur.PolygonInfinitesimalStages
