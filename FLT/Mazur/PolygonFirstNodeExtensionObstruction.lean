/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodePositiveExtension

/-!
# The exact obstruction to extending a first-order Laurent coordinate

The nonpositive tail vanishes if and only if the full coordinate extends to
an original node endomorphism reducing to the identity. In that case the
explicit positive-part construction supplies an automorphism. Thus the tail
is intrinsic to the extension problem, not an artifact of the chosen lift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPositivePart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable {R : Type} [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)

/-- Every genuine extension forces the omitted tail to vanish, independently of its construction. -/
theorem firstNodeExtension_boundaryTail_zero (q : R[T;T⁻¹])
    (f : (B) →ₐ[S] (B)) (hf : ∀ z, firstNodeReduction R (f z) = firstNodeReduction R z)
    (hx : leftLaurentMap (e) (f (leftCoordinate (e))) = (firstOrderCoordinateUnit q).val) :
    boundaryTail q = 0 := by
  apply (boundaryTail_eq_zero_iff q).mpr
  intro d hd
  exact firstOrderLaurentCoordinate_boundary_coeff q (firstNodeBoundaryPolynomial R f hf)
    ((firstNodeBoundaryPolynomial_toLaurent R f hf).trans
      (hx.trans (firstOrderCoordinateUnit_val q)))
    (firstNodeBoundaryPolynomial_coeff_zero R f hf) d hd

/-- The computed tail is the exact obstruction to existence of any original node extension. -/
theorem exists_firstNodeExtension_iff (q : R[T;T⁻¹]) :
    (∃ f : (B) →ₐ[S] (B),
      (∀ z, firstNodeReduction R (f z) = firstNodeReduction R z) ∧
      leftLaurentMap (e) (f (leftCoordinate (e))) = (firstOrderCoordinateUnit q).val) ↔
        boundaryTail q = 0 := by
  constructor
  · rintro ⟨f, hf, hx⟩
    exact firstNodeExtension_boundaryTail_zero q f hf hx
  · intro he
    exact ⟨(firstNodePositiveExtension q).toAlgHom, firstNodePositiveExtension_reduction q,
      (firstNodePositiveExtension_exact_iff q).mpr he⟩

/-- When any such extension exists, an explicit original-node automorphism already supplies it. -/
theorem exists_firstNodeAutomorphism_iff (q : R[T;T⁻¹]) :
    (∃ f : (B) ≃ₐ[S] (B),
      (∀ z, firstNodeReduction R (f z) = firstNodeReduction R z) ∧
      leftLaurentMap (e) (f (leftCoordinate (e))) = (firstOrderCoordinateUnit q).val) ↔
        boundaryTail q = 0 := by
  constructor
  · rintro ⟨f, hf, hx⟩
    exact firstNodeExtension_boundaryTail_zero q f.toAlgHom hf hx
  · intro he
    exact ⟨firstNodePositiveExtension q, firstNodePositiveExtension_reduction q,
      (firstNodePositiveExtension_exact_iff q).mpr he⟩

end FLT.Mazur.PolygonInfinitesimalStages
