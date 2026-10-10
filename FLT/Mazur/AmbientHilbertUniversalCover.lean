/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertChartUniversalFamily

/-!
# The actual ambient cover for universal Hilbert family descent

Base changing the constructed Hilbert chart cover gives an open cover of the
original ambient over the glued parameter scheme. Its objects are the exact
intrinsic ambients carrying the extended universal chart families.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ)

/-- The actual ambient chart above an affine Hilbert parameter chart. -/
def universalAmbientChart (i : A.Index) :
    pullback (A.chartBase d i) z ⟶ pullback (A.gluedBase d) z :=
  relativeIdealAmbientMap z (A.gluedBase d) (A.chartBase d i)
    (A.hilbertChart d i) (A.hilbertChart_over d i)

/-- The ambient chart square is cartesian over the actual Hilbert chart embedding. -/
theorem universalAmbientChart_isPullback (i : A.Index) :
    IsPullback (A.universalAmbientChart d i) (pullback.fst _ _)
      (pullback.fst _ _) (A.hilbertChart d i) :=
  relativeIdealAmbientMap_isPullback ..

instance (i : A.Index) : IsOpenImmersion (A.universalAmbientChart d i) :=
  MorphismProperty.of_isPullback (A.universalAmbientChart_isPullback d i).flip
    (inferInstance : IsOpenImmersion (A.hilbertChart d i))

/-- The intrinsic universal-chart ambients cover the ambient over the glued parameter scheme. -/
def universalAmbientCover : (pullback (A.gluedBase d) z).OpenCover where
  I₀ := A.Index
  X i := pullback (A.chartBase d i) z
  f := A.universalAmbientChart d
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    let C := (A.hilbertOpenCover d).pullback₁ (pullback.fst (A.gluedBase d) z)
    obtain ⟨i, y, hy⟩ := Scheme.Cover.exists_eq C x
    let q := A.universalAmbientChart_isPullback d i
    exact ⟨i, q.isoPullback.inv y,
      (congrArg (fun f ↦ f y) q.isoPullback_inv_fst).trans hy⟩

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
