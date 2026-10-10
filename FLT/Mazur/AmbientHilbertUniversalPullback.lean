/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertUniversalFamily

/-!
# Full universal pullback over arbitrary Hilbert parameters

Every morphism into the glued Hilbert scheme gives a full finite locally
free ideal family. This operation is natural under arbitrary base change
and recovers the classified full ideal on every original affine chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Actual parameters of the glued Hilbert scheme over an arbitrary test scheme. -/
def GluedParameters := { f : X ⟶ A.gluedHilbert d // f ≫ A.gluedBase d = s }

/-- Every actual glued parameter pulls back the constructed full universal family. -/
def parameterFamily (p : A.GluedParameters d s) : RelativeIdealFamilies z d s :=
  relativeIdealFamilyBaseChange z d (A.gluedBase d) s p.val p.property (A.universalFamily d)

/-- Original affine Hilbert parameters give actual parameters of the glued scheme. -/
def chartParameter (i : A.Index)
    (p : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s) :
    A.GluedParameters d s :=
  ⟨p.val ≫ A.hilbertChart d i, by rw [Category.assoc, A.hilbertChart_over, p.property]⟩

/-- Global universal pullback recovers every full ideal classified in an original affine chart. -/
theorem parameterFamily_chart (i : A.Index)
    (p : AmbientSchemeParameters R (A.Vars i) d (A.relations i) s) :
    A.parameterFamily d s (A.chartParameter d s i p) = A.chartParameterFamily d s i p := by
  unfold parameterFamily chartParameter
  rw [← relativeIdealFamilyBaseChange_comp z d (A.gluedBase d) (A.chartBase d i) s
    (A.hilbertChart d i) (A.hilbertChart_over d i) p.val p.property,
    A.universalFamily_chart, A.chartUniversalFamily_pullback]

/-- The global universal pullback commutes with arbitrary morphisms of test schemes. -/
theorem parameterFamily_natural (t : Y ⟶ Spec (.of R)) (g : Y ⟶ X) (hg : g ≫ s = t)
    (p : A.GluedParameters d s) :
    relativeIdealFamilyBaseChange z d s t g hg (A.parameterFamily d s p) =
      A.parameterFamily d t ⟨g ≫ p.val, by rw [Category.assoc, p.property, hg]⟩ :=
  relativeIdealFamilyBaseChange_comp z d (A.gluedBase d) s t p.val p.property g hg
    (A.universalFamily d)

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
