/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonScalingNaturality

/-!
# Injectivity of the Laurent coefficient map

The coordinate-preserving Laurent map is the coefficientwise monoid-algebra
map. Consequently an injective coefficient map remains injective.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonScalingNaturality
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The geometric coefficient map is the coefficientwise Laurent ring map. -/
theorem coeffMap_eq_mapRingHom (f : R →+* S) :
    coeffMap f = AddMonoidAlgebra.mapRingHom ℤ f := by
  apply ringHom_ext
  · intro r
    rw [coeffMap_C]
    exact (AddMonoidAlgebra.mapRingHom_single f 0 r).symm
  · rw [coeffMap_T_one]
    change AddMonoidAlgebra.single 1 1 = _
    rw [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]
  · rw [coeffMap_T_neg_one]
    change AddMonoidAlgebra.single (-1) 1 = _
    rw [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]

/-- Injective changes of coefficients retain every Laurent polynomial. -/
theorem coeffMap_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  rw [coeffMap_eq_mapRingHom]
  exact AddMonoidAlgebra.map_injective f.toAddMonoidHom hf

end FLT.Mazur.PolygonScalingNaturality
