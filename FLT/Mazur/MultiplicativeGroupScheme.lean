/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# The smooth multiplicative group scheme

The Laurent Hopf algebra represents a commutative group over any base ring.
Its structure morphism is smooth because Laurent polynomials are the
localization of a polynomial algebra away from its coordinate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open scoped Polynomial LaurentPolynomial TensorProduct

namespace FLT.Mazur.MultiplicativeGroupScheme

universe u
variable (R : Type u) [CommRing R]

/-- The multiplicative group over the spectrum of the base ring. -/
abbrev gm : Over (Spec (CommRingCat.of R)) :=
  (Spec (CommRingCat.of R[T;T⁻¹])).asOver (Spec (CommRingCat.of R))

instance commGrpObj : CommGrpObj (gm R) := inferInstance

/-- Laurent polynomials are smooth over their coefficient ring. -/
theorem smooth_laurent : Algebra.Smooth R R[T;T⁻¹] := by
  let : Algebra.Smooth R R[X] := {}
  let : Algebra.Smooth R[X] R[T;T⁻¹] :=
    Algebra.Smooth.of_isLocalization_Away Polynomial.X
  let : IsScalarTower R R[X] R[T;T⁻¹] :=
    IsScalarTower.of_algebraMap_eq fun r => (Polynomial.toLaurent_C r).symm
  exact Algebra.Smooth.comp R R[X] R[T;T⁻¹]

instance smooth : Smooth (gm R).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R R[T;T⁻¹]).Smooth
  rw [RingHom.smooth_algebraMap]
  exact smooth_laurent R

/-- Multiplication sends the coordinate to the product of the coordinates. -/
theorem comul_coordinate :
    Coalgebra.comul (R := R) (LaurentPolynomial.T 1 : R[T;T⁻¹]) =
      LaurentPolynomial.T 1 ⊗ₜ[R] LaurentPolynomial.T 1 :=
  LaurentPolynomial.comul_T 1

/-- The identity section evaluates the coordinate at one. -/
theorem counit_coordinate :
    Coalgebra.counit (R := R) (LaurentPolynomial.T 1 : R[T;T⁻¹]) = 1 :=
  LaurentPolynomial.counit_T 1

/-- Inversion replaces the coordinate by its inverse. -/
theorem antipode_coordinate :
    HopfAlgebra.antipode R (LaurentPolynomial.T 1 : R[T;T⁻¹]) =
      LaurentPolynomial.T (-1) :=
  LaurentPolynomial.antipode_T 1

/-- The scheme multiplication is induced by the Laurent comultiplication. -/
theorem multiplication_left :
    μ[gm R].left =
      (pullbackSpecIso (CommRingCat.of R) (CommRingCat.of R[T;T⁻¹])
        (CommRingCat.of R[T;T⁻¹])).hom ≫
      Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R R[T;T⁻¹])) :=
  mul_spec_asOver_spec_left

end FLT.Mazur.MultiplicativeGroupScheme
