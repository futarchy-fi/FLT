/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertUniversalFamily
public import FLT.Mazur.SmoothCurveFiberCartier

/-!
# Cartier fibers of the full universal Hilbert ideal

The constructed universal family is finite locally free. When the original
ambient is a smooth relative curve, every field-valued base change of its
full universal ideal is Cartier. This does not assert that the ideal is
Cartier over the entire Hilbert parameter scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
  [SmoothOfRelativeDimension 1 z]

/-- Arbitrary field-valued fibers of the full universal ideal are effective Cartier. -/
theorem universalIdeal_field_fiber_cartier {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ A.gluedHilbert d) :
    EffectiveCartier ((A.universalIdeal d).comap
      (pullback.fst (pullback.fst (A.gluedBase d) z) g)) := by
  let p := pullback.fst (A.gluedBase d) z
  let _ : SmoothOfRelativeDimension 1 p :=
    MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 1)
      (A.gluedBase d) z inferInstance
  let _ : IsFinite ((A.universalIdeal d).subschemeι ≫ p) :=
    (A.universalIdeal_degree d).1
  exact effectiveCartier_field_baseChange p (A.universalIdeal d) g

/-- The actual residue fibers of the universal ideal carry regular Cartier equations. -/
theorem universalIdeal_residue_fiber_cartier (s : A.gluedHilbert d) :
    EffectiveCartier ((A.universalIdeal d).comap
      ((pullback.fst (A.gluedBase d) z).fiberι s)) :=
  A.universalIdeal_field_fiber_cartier d ((A.gluedHilbert d).fromSpecResidueField s)

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
