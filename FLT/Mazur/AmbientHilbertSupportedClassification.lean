/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertUniversalPullback
public import FLT.Mazur.RelativeIdealSupportedRestriction

/-!
# Classification of full families supported in an original affine chart

An actual support containment supplies the affine classifying parameter.
Its global universal pullback recovers the full family, and its affine
parameter is unique. No common-affine-neighborhood existence is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) (i : A.Index)
variable (J : RelativeIdealFamilies z d s)
variable (hJ : Set.range J.val.subschemeι ⊆ Set.range
  (relativeIdealAmbientHom (A.originalChartBase i) z (A.chart i) (A.chart_over i) s))

/-- An actual family supported in an affine chart has an actual affine Hilbert parameter. -/
def supportedParameter : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s :=
  (ambientSchemeClassification R (A.Vars i) d (A.relations i) s).symm
    (relativeIdealFamilyRestriction (A.originalChartBase i) z
      (A.chart i) (A.chart_over i) s d J hJ)

/-- The affine parameter recovers the full original family after ambient extension. -/
theorem chartParameterFamily_supportedParameter :
    A.chartParameterFamily d s i (A.supportedParameter d s i J hJ) = J := by
  unfold chartParameterFamily supportedParameter
  rw [Equiv.apply_symm_apply]
  exact relativeIdealFamilyExtension_restriction _ _ _ _ _ _ _ _

/-- The global universal pullback recovers every full family supported in an original chart. -/
theorem parameterFamily_supportedParameter :
    A.parameterFamily d s (A.chartParameter d s i (A.supportedParameter d s i J hJ)) = J := by
  rw [A.parameterFamily_chart, A.chartParameterFamily_supportedParameter]

/-- Within the given affine chart, recovery of a full family determines the parameter uniquely. -/
theorem supportedParameter_unique
    (p : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s)
    (hp : A.chartParameterFamily d s i p = J) :
    p = A.supportedParameter d s i J hJ :=
  A.chartParameterFamily_injective d s i
    (hp.trans (A.chartParameterFamily_supportedParameter d s i J hJ).symm)

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
