/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSmoothFiniteFlatCartier
public import FLT.Mazur.AmbientHilbertUniversalFamily
public import FLT.Mazur.CartierSupportOpenDescent

/-!
# The full universal ideal on a smooth relative curve is Cartier

The actual finite locally free universal family on each affine ambient chart
is Cartier by the relative smooth-curve criterion. Its extension to the original
ambient is Cartier because the entire support stays in that open chart. The
constructed universal ambient cover then descends these Cartier equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.ClosedIdealCover
universe u
namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
  [SmoothOfRelativeDimension 1 z]

omit [IsSeparated z] in
/-- The original affine ambient chart inherits the smooth relative curve structure. -/
theorem originalChartBase_smooth_curve (i : A.Index) :
    SmoothOfRelativeDimension 1 (A.originalChartBase i) := by
  change SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (A.Vars i) R ⧸ A.relations i))))
  rw [← A.chart_over i]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (A.chart i ≫ z))

/-- The entire universal chart ideal is Cartier in the original ambient after base change. -/
theorem chartUniversalFamily_effectiveCartier (i : A.Index) :
    EffectiveCartier (A.chartUniversalFamily d i).val := by
  let _ := A.originalChartBase_smooth_curve i
  let _ : IsAffineHom (A.originalChartBase i) := by
    dsimp [originalChartBase]
    infer_instance
  let _ : IsAffineHom (pullback.fst (A.chartBase d i) (A.originalChartBase i)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let _ : SmoothOfRelativeDimension 1
      (pullback.fst (A.chartBase d i) (A.originalChartBase i)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  apply effectiveCartier_of_comap_of_support_subset _
    (relativeIdealAmbientHom (A.originalChartBase i) z
      (A.chart i) (A.chart_over i) (A.chartBase d i)) (A.chartUniversalFamily_support d i)
  rw [A.chartUniversalFamily_restrict]
  exact (relativeEffectiveCartier_of_affine_smooth_degree
    (pullback.fst (A.chartBase d i) (A.originalChartBase i))
    (ambientUniversalFamily R (A.Vars i) d (A.relations i)).val d
    (ambientUniversalFamily R (A.Vars i) d (A.relations i)).property).1

/-- The full descended universal ideal, including its nonreduced structure, is Cartier. -/
theorem universalIdeal_effectiveCartier : EffectiveCartier (A.universalIdeal d) := by
  rw [effectiveCartier_iff_openCover _ (A.universalAmbientCover d)]
  intro i
  change EffectiveCartier ((A.universalIdeal d).comap (A.universalAmbientChart d i))
  rw [A.universalIdeal_restrict]
  exact A.chartUniversalFamily_effectiveCartier d i

/-- Universal Cartier equations combine with the constructed degree to give a relative divisor. -/
theorem universalIdeal_relativeEffectiveCartier :
    RelativeEffectiveCartier (pullback.fst (A.gluedBase d) z) (A.universalIdeal d) :=
  ⟨A.universalIdeal_effectiveCartier d, (A.universalIdeal_degree d).2.1⟩

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
