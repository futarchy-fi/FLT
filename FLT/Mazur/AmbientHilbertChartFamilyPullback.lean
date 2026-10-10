/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertChartUniversalFamily
public import FLT.Mazur.RelativeIdealExtensionNaturality

/-!
# Pullback of full universal chart families

Every affine Hilbert parameter pulls the extended universal chart family back
to the extension of its classified full affine ideal. Thus universal chart
families already have their expected meaning on arbitrary test schemes in the
original separated ambient.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Every affine parameter classifies the full ideal extended into the original ambient. -/
def chartParameterFamily (i : A.Index)
    (p : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s) :
    RelativeIdealFamilies z d s :=
  relativeIdealFamilyExtension (A.originalChartBase i) z (A.chart i) (A.chart_over i) s d
    (ambientSchemeClassification R (A.Vars i) d (A.relations i) s p)

/-- Parameter pullback of the chart universal family recovers its full classified ideal. -/
theorem chartUniversalFamily_pullback (i : A.Index)
    (p : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s) :
    relativeIdealFamilyBaseChange z d (A.chartBase d i) s p.val p.property
        (A.chartUniversalFamily d i) = A.chartParameterFamily d s i p := by
  unfold chartUniversalFamily chartParameterFamily
  rw [relativeIdealFamilyExtension_natural]
  apply congrArg (relativeIdealFamilyExtension (A.originalChartBase i) z
    (A.chart i) (A.chart_over i) s d)
  apply Subtype.ext
  exact ambientSchemeClassification_universalPullback R (A.Vars i) d (A.relations i) s p

/-- Equal full affine classified ideals give equal extended families in the original ambient. -/
theorem chartParameterFamily_injective (i : A.Index) :
    Function.Injective (A.chartParameterFamily d s i) := by
  intro p q h
  have hv := congrArg (fun J : RelativeIdealFamilies z d s ↦
    J.val.comap (relativeIdealAmbientHom (A.originalChartBase i) z
      (A.chart i) (A.chart_over i) s)) h
  change (relativeIdealFamilyExtension _ _ _ _ _ _ _).val.comap _ =
    (relativeIdealFamilyExtension _ _ _ _ _ _ _).val.comap _ at hv
  rw [relativeIdealFamilyExtension_restrict, relativeIdealFamilyExtension_restrict] at hv
  exact (ambientSchemeClassification R (A.Vars i) d (A.relations i) s).injective
    (Subtype.ext hv)

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
