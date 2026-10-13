/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertChartChange
public import FLT.Mazur.RelativeFppfLocallyRingedCover

/-!
# Actual fppf covers of translated Hilbert parameters

An arbitrary fppf change of translation base induces an actual fppf parameter
cover. No section of the cover, or effectivity of a quotient, is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ)
  {V W : Over (Spec (.of R))} (b : W ⟶ V)

/-- Every base-change-stable property transfers to the actual parameter map. -/
theorem variableHilbertChange_property (P : MorphismProperty Scheme)
    [P.IsStableUnderBaseChange] (hb : P b.left) :
    P (baseMarkedChartChange f b d).left :=
  MorphismProperty.of_isPullback
    ((baseMarkedChartChange_isPullback f b d).map (Over.forget _)).flip hb

instance variableHilbertChange_flat [Flat b.left] :
    Flat (baseMarkedChartChange f b d).left :=
  variableHilbertChange_property f d b _ inferInstance

instance variableHilbertChange_locallyOfFinitePresentation [LocallyOfFinitePresentation b.left] :
    LocallyOfFinitePresentation (baseMarkedChartChange f b d).left :=
  variableHilbertChange_property f d b _ inferInstance

instance variableHilbertChange_etale [Etale b.left] :
    Etale (baseMarkedChartChange f b d).left :=
  variableHilbertChange_property f d b _ inferInstance

instance variableHilbertChange_smooth [Smooth b.left] :
    Smooth (baseMarkedChartChange f b d).left :=
  variableHilbertChange_property f d b _ inferInstance

instance variableHilbertChange_surjective [Surjective b.left] :
    Surjective (baseMarkedChartChange f b d).left :=
  variableHilbertChange_property f d b _ inferInstance

/-- The chart change covers all parameters, including those without a chosen lift. -/
theorem variableHilbertChange_fppf [Flat b.left] [LocallyOfFinitePresentation b.left]
    [Surjective b.left] :
    Presieve.singleton (baseMarkedChartChange f b d).left ∈
      Scheme.fppfPrecoverage (variableHilbertTest f d V).left :=
  Scheme.Hom.singleton_mem_fppfPrecoverage _

end FLT.Mazur.HilbertChart
