/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicChartIntersection
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Two-chart covers and their intersections after arbitrary base change -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A chart times an arbitrary scheme over the coefficient base. -/
def chartBaseChangeInclusion {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (b : Bool) :
    pullback (chartToBase W b) f ⟶ pullback (toBase W) f :=
  pullback.map _ _ _ _ (sourceChart W b) (𝟙 _) (𝟙 _) (by simp) (by simp)

instance chartBaseChangeInclusion_isOpenImmersion
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (b : Bool) :
    IsOpenImmersion (chartBaseChangeInclusion W f b) := by
  unfold chartBaseChangeInclusion
  infer_instance

/-- The original two-chart cover pulled back over an arbitrary coefficient-base morphism. -/
def chartBaseChangeCover {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) :
    (pullback (toBase W) f).OpenCover :=
  (Scheme.Pullback.openCoverOfLeft (sourceOpenCover W) (toBase W) f).copy Bool
    (fun b ↦ pullback (chartToBase W b) f) (chartBaseChangeInclusion W f) (Equiv.refl _)
    (fun b ↦ (pullback.congrHom (sourceChart_toBase W b) (rfl : f = f)).symm) (by
      intro b
      apply pullback.hom_ext <;>
        simp [chartBaseChangeInclusion, pullback.congrHom, sourceOpenCover] <;> rfl)

/-- Coefficient projection of the common chart overlap. -/
def chartOverlapToBase : Spec (.of (Overlap W true)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Overlap W true)))

/-- The two maps from the common overlap, in infinity-chart coordinates. -/
def chartOverlapMap : ∀ b, Spec (.of (Overlap W true)) ⟶ chart W b
  | false => Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom)
  | true => overlapInclusion W true

@[reassoc (attr := simp)] theorem chartOverlapMap_toBase (b : Bool) :
    chartOverlapMap W b ≫ chartToBase W b = chartOverlapToBase W := by
  cases b
  · change Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Ring W false))) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (changeChart W true).comp_algebraMap
  · change Spec.map (CommRingCat.ofHom (algebraMap (Ring W true) (Overlap W true))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Ring W true))) = _
    rw [← Spec.map_comp]
    congr 1

/-- The overlap included into either chart after arbitrary base change. -/
def chartOverlapBaseChangeMap {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (b : Bool) :
    pullback (chartOverlapToBase W) f ⟶ pullback (chartToBase W b) f :=
  pullback.map _ _ _ _ (chartOverlapMap W b) (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The same explicit overlap remains the actual intersection after base change. -/
theorem chartOverlap_baseChange_isPullback
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) :
    IsPullback (chartOverlapBaseChangeMap W f false) (chartOverlapBaseChangeMap W f true)
      (chartBaseChangeInclusion W f false) (chartBaseChangeInclusion W f true) := by
  let U : Over (Spec (.of R)) := Over.mk (chartOverlapToBase W)
  let A : Over (Spec (.of R)) := Over.mk (chartToBase W false)
  let B : Over (Spec (.of R)) := Over.mk (chartToBase W true)
  let E : Over (Spec (.of R)) := Over.mk (toBase W)
  let a : U ⟶ A := Over.homMk (chartOverlapMap W false) (chartOverlapMap_toBase W false)
  let b : U ⟶ B := Over.homMk (chartOverlapMap W true) (chartOverlapMap_toBase W true)
  let i : A ⟶ E := Over.homMk (sourceChart W false) (sourceChart_toBase W false)
  let j : B ⟶ E := Over.homMk (sourceChart W true) (sourceChart_toBase W true)
  have h : IsPullback a b i j :=
    IsPullback.of_map_of_faithful (Over.forget _) (chart_overlap_true_isPullback W)
  have h' := (h.map (Over.pullback f)).map (Over.forget X)
  dsimp only [U, A, B, E, a, b, i, j] at h'
  simpa only [Over.forget_map, Over.forget_obj, Over.pullback_obj_left, Over.mk_hom,
    Over.pullback_map_left, Over.homMk_left, Category.comp_id,
    chartOverlapBaseChangeMap, chartBaseChangeInclusion, pullback.map] using h'

end WeierstrassCurve.CubicCharts
