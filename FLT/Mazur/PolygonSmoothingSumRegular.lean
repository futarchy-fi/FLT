/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingFlat
public import FLT.Mazur.RegularPrincipalOpenLiftExt
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# A regular principal open in every arithmetic node chart

The sum x+y is a nonzerodivisor in R[x,y]/(xy-t), including over
nonreduced coefficient rings. Its principal open therefore detects maps
to separated targets without discarding any infinitesimal information.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)

/-- The sum coordinate is regular in the monic quadratic presentation. -/
theorem sumCoordinate_regular : IsRegular (sumCoordinate t) := by
  apply (Commute.isRegular_iff (fun b ↦ mul_comm _ b)).mpr
  have hs := Module.Flat.isSMulRegular_of_isRegular
    (M := QuadraticModel t) (Polynomial.isRegular_X (R := R))
  intro a b hab
  apply hs
  simpa only [Algebra.smul_def, sumCoordinate, AdjoinRoot.algebraMap_eq] using hab

/-- The original sum of branch coordinates is regular over every coefficient ring. -/
theorem branchSum_regular : IsRegular (leftCoordinate t + rightCoordinate t) := by
  apply (Commute.isRegular_iff (fun b ↦ mul_comm _ b)).mpr
  intro a b hab
  apply (quadraticEquiv t).injective
  apply (sumCoordinate_regular t).left
  have he := congrArg (quadraticEquiv t) hab
  simpa only [map_mul, map_add, quadraticEquiv, AlgEquiv.ofAlgHom_apply,
    chartToQuadratic_left, chartToQuadratic_right, sub_add_cancel] using he

/-- The original principal open D(x+y) is schematically dense in the whole node chart. -/
theorem branchSum_schematicallyDense :
    IsSchemeTheoreticallyDominant
      (PrincipalAffineRefinement.inclusion (leftCoordinate t + rightCoordinate t)) :=
  RegularPrincipalOpen.inclusion_schematicallyDense _ (branchSum_regular t)

/-- Equality on D(x+y) determines full arithmetic chart maps to a separated target. -/
theorem branchSum_hom_ext {Y S : Scheme} (s : Y ⟶ S) [IsSeparated s]
    (f g : chart R t ⟶ Y) (hb : f ≫ s = g ≫ s)
    (he : PrincipalAffineRefinement.inclusion (leftCoordinate t + rightCoordinate t) ≫ f =
      PrincipalAffineRefinement.inclusion (leftCoordinate t + rightCoordinate t) ≫ g) :
    f = g := by
  let _ := branchSum_schematicallyDense t
  exact Chow.schematicallyDense_ext s hb _ he

end FLT.Mazur.PolygonSmoothing
