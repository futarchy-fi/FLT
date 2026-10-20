/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityAlgebra
public import FLT.Mazur.LaurentUnitPoints

/-!
# The roots-of-unity functor on algebras

Points of the character algebra are exactly units whose nth power is one.
The equivalence retains the inclusion into the Laurent functor and commutes
with maps of test algebras, without reducedness or characteristic hypotheses.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped LaurentPolynomial

namespace FLT.Mazur.RootsOfUnityAlgebraPoints

open RootsOfUnityAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (n : ℕ) [NeZero n]

/-- A root of unity defines a character of Z/n by its powers. -/
def character (a : Aˣ) (ha : a ^ n = 1) : Multiplicative (ZMod n) →* A where
  toFun i := (a ^ i.toAdd.val : Aˣ).val
  map_one' := by simp
  map_mul' i j := by
    change ((a ^ (i.toAdd + j.toAdd).val : Aˣ) : A) = _
    rw [ZMod.val_add, ← Units.val_mul, ← pow_add]
    exact congrArg Units.val (pow_eq_pow_mod _ ha).symm

/-- Evaluate each residue character at the corresponding power of a root. -/
def evalRoot (a : Aˣ) (ha : a ^ n = 1) : Coordinate R n →ₐ[R] A :=
  AddMonoidAlgebra.lift R A (ZMod n) (character n a ha)

theorem evalRoot_single (a : Aˣ) (ha : a ^ n = 1) (i : ZMod n) (r : R) :
    evalRoot (R := R) n a ha (AddMonoidAlgebra.single i r) =
      algebraMap R A r * (a ^ i.val : Aˣ).val := by
  simp [evalRoot, AddMonoidAlgebra.lift_single, character, Algebra.smul_def]

/-- Natural exponents evaluate to the original powers, not just chosen representatives. -/
theorem evalRoot_natCast (a : Aˣ) (ha : a ^ n = 1) (k : ℕ) :
    evalRoot (R := R) n a ha (AddMonoidAlgebra.single (k : ZMod n) 1) =
      (a ^ k : Aˣ).val := by
  rw [evalRoot_single, map_one, one_mul, ZMod.val_natCast]
  exact congrArg Units.val (pow_eq_pow_mod _ ha).symm

/-- Every character is a power of the universal root. -/
theorem rootUnit_val_pow (i : ZMod n) :
    (rootUnit R n).val ^ i.val = AddMonoidAlgebra.single i 1 := by
  simp [rootUnit, AddMonoidAlgebra.single_pow]

/-- An algebra map is determined by the image of the universal root. -/
theorem hom_ext {f g : Coordinate R n →ₐ[R] A}
    (h : f (rootUnit R n).val = g (rootUnit R n).val) : f = g := by
  apply AddMonoidAlgebra.algHom_ext
  · intro i
    rw [← rootUnit_val_pow n i, map_pow, map_pow, h]
  · ext

/-- Read the universal root in a test algebra. -/
def pointRoot (f : Coordinate R n →ₐ[R] A) : {a : Aˣ // a ^ n = 1} :=
  ⟨Units.map f.toMonoidHom (rootUnit R n), by
    rw [← map_pow, rootUnit_pow, map_one]⟩

/-- Evaluation recovers the root as a unit, including its inverse. -/
theorem pointRoot_evalRoot (a : Aˣ) (ha : a ^ n = 1) :
    pointRoot n (evalRoot (R := R) n a ha) = ⟨a, ha⟩ := by
  apply Subtype.ext
  apply Units.ext
  change evalRoot n a ha (AddMonoidAlgebra.single (1 : ZMod n) 1) = a.val
  simpa using evalRoot_natCast (R := R) n a ha 1

/-- Reading then evaluating recovers every algebra map. -/
theorem evalRoot_pointRoot (f : Coordinate R n →ₐ[R] A) :
    evalRoot n (pointRoot n f).val (pointRoot n f).property = f := by
  apply hom_ext n
  change evalRoot n (pointRoot n f).val (pointRoot n f).property
    (AddMonoidAlgebra.single 1 1) = (pointRoot n f).val.val
  simpa only [pow_one, Nat.cast_one] using
    evalRoot_natCast (R := R) n (pointRoot n f).val (pointRoot n f).property 1

/-- The character algebra represents the nth roots of unity on all algebra tests. -/
def pointsEquiv : (Coordinate R n →ₐ[R] A) ≃ {a : Aˣ // a ^ n = 1} where
  toFun := pointRoot n
  invFun a := evalRoot n a.val a.property
  left_inv := evalRoot_pointRoot n
  right_inv a := pointRoot_evalRoot n a.val a.property

omit [NeZero n] in
/-- The Laurent restriction retains the same unit. -/
theorem pointRoot_restriction (f : Coordinate R n →ₐ[R] A) :
    LaurentUnitPoints.pointUnit (f.comp (restriction R n).toAlgHom) =
      (pointRoot n f).val := by
  apply Units.ext
  change f (restriction R n (LaurentPolynomial.T 1)) = f (rootUnit R n).val
  rw [restriction_T]
  simp only [Int.cast_one, rootUnit]

omit [NeZero n] in
/-- Reading a point is natural in the test algebra. -/
theorem pointRoot_natural {B : Type*} [CommRing B] [Algebra R B]
    (g : A →ₐ[R] B) (f : Coordinate R n →ₐ[R] A) :
    (pointRoot n (g.comp f)).val = Units.map g.toMonoidHom (pointRoot n f).val := by
  apply Units.ext
  rfl

end FLT.Mazur.RootsOfUnityAlgebraPoints
