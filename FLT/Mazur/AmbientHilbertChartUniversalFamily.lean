/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertGluedBase
public import FLT.Mazur.HilbertAmbientUniversalFamily
public import FLT.Mazur.RelativeIdealOpenExtension

/-!
# Full universal chart families in the original separated ambient

Each actual affine Hilbert universal ideal extends into the original ambient
scheme after base change to its parameter chart. The resulting full family
has degree d, stays supported in the original ambient chart, and restricts
back to the complete affine universal ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]

/-- The coefficient structure of an original quotient ambient chart. -/
abbrev originalChartBase (i : A.Index) :
    Spec (.of (MvPolynomial (A.Vars i) R ⧸ A.relations i)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (A.Vars i) R ⧸ A.relations i)))

/-- The actual universal family on a parameter chart, extended into the original ambient. -/
def chartUniversalFamily (i : A.Index) : RelativeIdealFamilies z d (A.chartBase d i) :=
  relativeIdealFamilyExtension (A.originalChartBase i) z (A.chart i) (A.chart_over i)
    (A.chartBase d i) d (ambientUniversalFamily R (A.Vars i) d (A.relations i))

/-- The extended universal chart family has the requested actual finite locally free degree. -/
theorem chartUniversalFamily_degree (i : A.Index) :
    FiniteLocallyFreeDegree ((A.chartUniversalFamily d i).val.subschemeι ≫
      pullback.fst (A.chartBase d i) z) d := (A.chartUniversalFamily d i).property

/-- The extended universal chart family is still supported in its original ambient chart. -/
theorem chartUniversalFamily_support (i : A.Index) :
    Set.range (A.chartUniversalFamily d i).val.subschemeι ⊆
      Set.range (relativeIdealAmbientHom (A.originalChartBase i) z
        (A.chart i) (A.chart_over i) (A.chartBase d i)) :=
  relativeIdealFamilyExtension_support ..

/-- Restriction recovers the entire affine universal ideal, including its nilpotent structure. -/
theorem chartUniversalFamily_restrict (i : A.Index) :
    (A.chartUniversalFamily d i).val.comap
        (relativeIdealAmbientHom (A.originalChartBase i) z
          (A.chart i) (A.chart_over i) (A.chartBase d i)) =
      (ambientUniversalFamily R (A.Vars i) d (A.relations i)).val :=
  relativeIdealFamilyExtension_restrict ..

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
