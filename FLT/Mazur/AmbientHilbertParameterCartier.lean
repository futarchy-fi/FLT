/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertUniversalCartier
public import FLT.Mazur.AmbientHilbertUniversalPullback
public import FLT.Mazur.RelativeCartierBaseChange

/-!
# Cartier divisors for arbitrary universal Hilbert parameters

The full universal Cartier ideal pulls back over every test scheme. The
existing cartesian comparison identifies this pullback with the actual
parameter family's ideal, including its nilpotent structure.
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
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Every actual parameter family is a relative Cartier divisor over its test scheme. -/
theorem parameterFamily_relativeEffectiveCartier (p : A.GluedParameters d s) :
    RelativeEffectiveCartier (pullback.fst s z) (A.parameterFamily d s p).val := by
  refine ⟨?_, (A.parameterFamily d s p).property.2.1⟩
  have h := relativeCartierBaseChange (pullback.fst (A.gluedBase d) z) p.val
    (A.universalIdeal d) (A.universalIdeal_relativeEffectiveCartier d)
  let H := relativeIdealAmbientMap_isPullback z (A.gluedBase d) s p.val p.property
  have hc := h.1.comap_of_isOpenImmersion H.isoPullback.hom
  rw [← Scheme.IdealSheafData.comap_comp, H.isoPullback_hom_fst] at hc
  exact hc

/-- Original affine-chart parameters give Cartier divisors in the original ambient. -/
theorem chartParameterFamily_relativeEffectiveCartier (i : A.Index)
    (p : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s) :
    RelativeEffectiveCartier (pullback.fst s z) (A.chartParameterFamily d s i p).val := by
  rw [← A.parameterFamily_chart d s i p]
  exact A.parameterFamily_relativeEffectiveCartier d s (A.chartParameter d s i p)

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
