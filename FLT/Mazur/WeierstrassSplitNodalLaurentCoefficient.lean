/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalLaurent

/-!
# The normalized nodal Laurent coordinates commute with coefficient maps

The coefficient map fixes the torus character and carries both normalized
coordinates to the coordinates for the mapped tangent unit.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
variable {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)

/-- Change Laurent coefficients while keeping the original torus character. -/
def nodalLaurentCoefficientMap : S[T;T⁻¹] →+* T[T;T⁻¹] :=
  AddMonoidAlgebra.mapRingHom ℤ f

/-- The actual coefficient morphism preserves the entire coefficient ring. -/
theorem nodalLaurentCoefficientMap_scalar (s : S) :
    nodalLaurentCoefficientMap f (algebraMap S S[T;T⁻¹] s) =
      algebraMap T T[T;T⁻¹] (f s) := by
  exact AddMonoidAlgebra.mapRingHom_single f 0 s

/-- Every torus character is unchanged by coefficient specialization. -/
@[simp] theorem nodalLaurentCoefficientMap_character (n : ℤ) :
    nodalLaurentCoefficientMap f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ f (.single n 1) = .single n 1
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

/-- The normalized X coordinate specializes with its actual tangent unit. -/
@[simp] theorem splitNodalLaurentX_coefficient (a : Sˣ) :
    nodalLaurentCoefficientMap f (splitNodalLaurentX a) =
      splitNodalLaurentX (Units.map f a) := by
  simp only [splitNodalLaurentX, map_mul, map_sub, map_one,
    nodalLaurentCoefficientMap_scalar, nodalLaurentCoefficientMap_character]
  rfl

/-- The normalized Z coordinate specializes, including at the identity of the torus. -/
@[simp] theorem splitNodalLaurentZ_coefficient (a : Sˣ) :
    nodalLaurentCoefficientMap f (splitNodalLaurentZ a) =
      splitNodalLaurentZ (Units.map f a) := by
  simp only [splitNodalLaurentZ, map_mul, map_pow, splitNodalLaurentX_coefficient,
    nodalLaurentCoefficientMap_character]

end FLT.Mazur.WeierstrassIntegralChart
