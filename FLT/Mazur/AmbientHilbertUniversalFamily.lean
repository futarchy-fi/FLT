/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertUniversalIdeal

/-!
# The global finite locally free universal Hilbert family

The descended full ideal has finite locally free degree d by its cartesian
restrictions to the actual Hilbert chart cover. Its full family restriction
recovers each original universal chart family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]

/-- The descended global full ideal has actual finite locally free degree d. -/
theorem universalIdeal_degree :
    FiniteLocallyFreeDegree ((A.universalIdeal d).subschemeι ≫
      pullback.fst (A.gluedBase d) z) d := by
  let J := A.universalIdeal d
  apply finiteLocallyFreeDegree_of_cartesianCover _ (A.hilbertOpenCover d)
    (fun i ↦ (J.comap (A.universalAmbientChart d i)).subscheme)
    (fun i ↦ restrictionMap J (A.universalAmbientChart d i))
    (fun i ↦ (J.comap (A.universalAmbientChart d i)).subschemeι ≫
      pullback.fst (A.chartBase d i) z)
    (fun i ↦ restrictionMap_base_isPullback J _ (A.universalAmbientChart_isPullback d i)) d
  intro i
  change FiniteLocallyFreeDegree (((A.universalIdeal d).comap
    (A.universalAmbientChart d i)).subschemeι ≫ pullback.fst (A.chartBase d i) z) d
  rw [A.universalIdeal_restrict d i]
  exact A.chartUniversalFamily_degree d i

/-- The actual global universal family over the constructed glued Hilbert scheme. -/
def universalFamily : RelativeIdealFamilies z d (A.gluedBase d) :=
  ⟨A.universalIdeal d, A.universalIdeal_degree d⟩

/-- Universal family pullback to each original Hilbert chart recovers its full ideal. -/
theorem universalFamily_chart (i : A.Index) :
    relativeIdealFamilyBaseChange z d (A.gluedBase d) (A.chartBase d i)
      (A.hilbertChart d i) (A.hilbertChart_over d i) (A.universalFamily d) =
        A.chartUniversalFamily d i := by
  apply Subtype.ext
  exact A.universalIdeal_restrict d i

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
