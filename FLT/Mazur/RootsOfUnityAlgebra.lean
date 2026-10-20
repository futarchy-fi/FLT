/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The coordinate Hopf algebra of roots of unity

The group algebra of Z/n represents the diagonalizable group of nth roots of
unity, over arbitrary coefficient rings. Reduction of Laurent exponents gives
its surjective coordinate map from the multiplicative group.
-/

@[expose] public noncomputable section

open scoped LaurentPolynomial

namespace FLT.Mazur.RootsOfUnityAlgebra

variable (R : Type*) [CommRing R] (n : ℕ)

/-- Coordinates on the diagonalizable group with character group Z/n. -/
abbrev Coordinate := AddMonoidAlgebra R (ZMod n)

/-- Restriction of Laurent functions reduces the exponent modulo n. -/
def restriction : R[T;T⁻¹] →ₐc[R] Coordinate R n :=
  AddMonoidAlgebra.mapDomainBialgHom R (Int.castAddHom (ZMod n))

theorem restriction_single (i : ℤ) (r : R) :
    restriction R n (AddMonoidAlgebra.single i r) =
      AddMonoidAlgebra.single (i : ZMod n) r :=
  AddMonoidAlgebra.mapDomainBialgHom_single _ _ _

@[simp]
theorem restriction_T (i : ℤ) :
    restriction R n (LaurentPolynomial.T i) =
      AddMonoidAlgebra.single (i : ZMod n) 1 :=
  restriction_single R n i 1

/-- Every residue character lifts to a Laurent monomial. -/
theorem restriction_surjective : Function.Surjective (restriction R n) := by
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | single i r =>
    obtain ⟨j, rfl⟩ := ZMod.intCast_surjective i
    exact ⟨AddMonoidAlgebra.single j r, restriction_single R n j r⟩

/-- The universal root and its inverse are opposite characters. -/
def rootUnit : (Coordinate R n)ˣ where
  val := AddMonoidAlgebra.single 1 1
  inv := AddMonoidAlgebra.single (-1) 1
  val_inv := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  inv_val := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

/-- The universal root satisfies its defining nth-power relation. -/
theorem rootUnit_pow : rootUnit R n ^ n = 1 := by
  apply Units.ext
  simp [rootUnit, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.one_def]

/-- The characters give an explicit basis of size n, including over the zero ring. -/
def basis [NeZero n] : Module.Basis (Fin n) R (Coordinate R n) :=
  (AddMonoidAlgebra.basis (ZMod n) R).reindex (ZMod.finEquiv n).symm.toEquiv

instance free [NeZero n] : Module.Free R (Coordinate R n) :=
  Module.Free.of_basis (basis R n)

instance finite [NeZero n] : Module.Finite R (Coordinate R n) :=
  Module.Finite.of_basis (basis R n)

end FLT.Mazur.RootsOfUnityAlgebra
