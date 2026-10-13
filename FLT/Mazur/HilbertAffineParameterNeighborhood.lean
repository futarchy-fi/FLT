/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIdentityGroundBase

/-!
# Actual affine open parameter neighborhoods

Choose an affine open around any point of the original Hilbert parameter
scheme. The inclusion is open even when the original test-to-parameter map
is not, and the selected point maps to the prescribed original parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart.AffineParameterNeighborhood
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
variable (p : (variableHilbertTest f d V).left)

/-- The original parameter scheme's affine open cover. -/
def cover := (variableHilbertTest f d V).left.affineOpenCover

/-- An affine source over the original ground base through the prescribed Hilbert parameter. -/
def source : Over (Spec (.of R)) :=
  Over.mk ((cover f d V).f ((cover f d V).idx p) ≫ (variableHilbertTest f d V).hom)

/-- Its actual open parameter inclusion. -/
def chart : source f d V p ⟶ variableHilbertTest f d V :=
  Over.homMk ((cover f d V).f ((cover f d V).idx p))

instance source_affine : IsAffine (source f d V p).left :=
  inferInstanceAs (IsAffine (Spec ((cover f d V).X ((cover f d V).idx p))))

instance chart_openImmersion : IsOpenImmersion (chart f d V p).left :=
  inferInstanceAs (IsOpenImmersion ((cover f d V).f ((cover f d V).idx p)))

/-- A selected point of the constructed affine source. -/
def point : (source f d V p).left := ((cover f d V).covers p).choose

/-- No original parameter point is lost by the affine restriction. -/
theorem point_chart : (chart f d V p).left (point f d V p) = p :=
  ((cover f d V).covers p).choose_spec

end FLT.Mazur.HilbertChart.AffineParameterNeighborhood
