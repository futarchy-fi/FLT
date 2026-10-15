/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingMarkedSection
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# Full punctured-node maps are detected by their unit coordinate

Once the first node coordinate has a specified unit image, the node equation
forces the second coordinate. Thus a coordinate extension gives the full
Laurent algebra comparison and the entire original branch square of schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentUnitPoints
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R)

/-- A map out of the actual node is determined by a unit image of its left coordinate. -/
theorem nodeMap_eq_of_left_unit {S : Type} [CommRing S] [Algebra R S]
    (f g : ChartRing t →ₐ[R] S) (u : Sˣ)
    (hf : f (leftCoordinate t) = u.val) (hg : g (leftCoordinate t) = u.val) : f = g := by
  apply chartRing_hom_ext t
  · exact hf.trans hg.symm
  · apply u.isUnit.mul_left_cancel
    have hfr := congrArg f (coordinate_relation t)
    have hgr := congrArg g (coordinate_relation t)
    rw [map_mul, hf, AlgHom.commutes] at hfr
    rw [map_mul, hg, AlgHom.commutes] at hgr
    exact hfr.trans hgr.symm

/-- Agreement on the first coordinate gives the entire original Laurent restriction. -/
theorem leftLaurentMap_comp_eq_eval (f : ChartRing t →ₐ[R] ChartRing t)
    (u : R[T;T⁻¹]ˣ) (hx : leftLaurentMap t (f (leftCoordinate t)) = u.val) :
    (leftLaurentMap t).comp f = (evalUnit u).comp (leftLaurentMap t) := by
  apply nodeMap_eq_of_left_unit t _ _ u hx
  simp only [AlgHom.comp_apply, leftLaurentMap_left, evalUnit_T, zpow_one]

/-- The full original punctured-branch square follows from the unit coordinate extension. -/
theorem leftBranchOpen_comp_spec_eq (f : ChartRing t →ₐ[R] ChartRing t)
    (u : R[T;T⁻¹]ˣ) (hx : leftLaurentMap t (f (leftCoordinate t)) = u.val) :
    leftBranchOpen R t ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom (evalUnit u).toRingHom) ≫ leftBranchOpen R t := by
  rw [leftBranchOpen_eq_spec, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (leftLaurentMap_comp_eq_eval t f u hx))

end FLT.Mazur.PolygonSmoothing
