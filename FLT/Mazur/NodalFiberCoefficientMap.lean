/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberAlgebra

/-!
# Coefficient maps between complete smoothing nodes

The original coefficient homomorphism and equality of the smoothing constants
induce a map of the entire node algebras, fixing both labeled coordinates.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (c : R) (d : S) (hc : algebraMap R S c = d)

/-- Extend the original coefficients while preserving both complete node coordinates. -/
def coefficientMap : Coordinate c →ₐ[R] Coordinate d :=
  evaluation c (p d) (q d) (by
    rw [relation, IsScalarTower.algebraMap_apply R S (Coordinate d), hc])

/-- The first node coordinate keeps its label under coefficient extension. -/
@[simp] theorem coefficientMap_p : coefficientMap c d hc (p c) = p d :=
  evaluation_p c _ _ _

/-- The second node coordinate keeps its label under coefficient extension. -/
@[simp] theorem coefficientMap_q : coefficientMap c d hc (q c) = q d :=
  evaluation_q c _ _ _

/-- Every original scalar uses the given coefficient extension. -/
theorem coefficientMap_scalar (a : R) :
    coefficientMap c d hc (algebraMap R (Coordinate c) a) =
      algebraMap S (Coordinate d) (algebraMap R S a) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S (Coordinate d)]

end FLT.Mazur.NodalFiber
