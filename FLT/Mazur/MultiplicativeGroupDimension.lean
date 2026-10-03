/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MultiplicativeGroupScheme
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The multiplicative group has relative dimension one

The Laurent algebra is a localization of the one-variable polynomial algebra.
Keeping its relative dimension supplies the hypothesis needed for Cartier
section divisors, over any coefficient ring.
-/

open AlgebraicGeometry
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.MultiplicativeGroupDimension
variable (R : Type u) [CommRing R]

/-- The Laurent algebra is standard smooth of relative dimension one. -/
theorem standardSmooth_laurent : Algebra.IsStandardSmoothOfRelativeDimension 1 R R[T;T⁻¹] := by
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 R R[X] :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.uniqueAlgEquiv R (Fin 1))
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 R[X] R[T;T⁻¹] :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away Polynomial.X
  let : IsScalarTower R R[X] R[T;T⁻¹] :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (Polynomial.toLaurent_C r).symm
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 R R[X] R[T;T⁻¹]

/-- The scheme-theoretic multiplicative group is smooth of relative dimension one. -/
instance dimension : SmoothOfRelativeDimension 1 (MultiplicativeGroupScheme.gm R).hom := by
  change SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap R R[T;T⁻¹])
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact standardSmooth_laurent R

end FLT.Mazur.MultiplicativeGroupDimension
