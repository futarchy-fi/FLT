/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPoints
public import FLT.GroupScheme.KummerPoints
public import FLT.GroupScheme.KummerTwist
public import FLT.GroupScheme.RaynaudExtension
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-! # Actual finite-flat split Kummer levels over the p-adic integers

The equations are X^(p^n) = 1 on each of p^n components. The point comparison
here reads these equations; identifying the standard representation's tensor
quotient and its local action is a separate obligation.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]

/-- The actual split Kummer coordinate algebra at level n. -/
abbrev SplitKummerCoordinate (n : ℕ) := KummerAlgebra.Coordinate ℤ_[p] (p ^ n) 1

/-- The split Kummer model, with its actual geometric-point Galois action. -/
def splitKummerModel (n : ℕ) : FF ℤ_[p] ℚ_[p] := by
  letI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let H := SplitKummerCoordinate p n
  letI : HopfAlgebra.IsFiniteFlat ℤ_[p] H :=
    KummerAlgebra.coordinate_isFiniteFlat ℤ_[p] (p ^ n) 1 (pow_pos (Fact.out : p.Prime).pos _)
  letI : Algebra.Etale ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] H) :=
    KummerAlgebra.generic_etale ℤ_[p] (p ^ n) 1 (pow_pos (Fact.out : p.Prime).pos _)
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast pow_ne_zero n (Fact.out : p.Prime).ne_zero))
  letI := HopfAlgebra.pointsCommGroup ℚ_[p] (AlgebraicClosure ℚ_[p]) (ℚ_[p] ⊗[ℤ_[p]] H)
  exact
    { CoordinateRing := H
      Points := Additive (ℚ_[p] ⊗[ℤ_[p]] H →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      points :=
        { toFun := id
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      points_bijective := Function.bijective_id }

/-- Reading the component and root gives all geometric points of the actual model. -/
def splitKummerCoordinates (n : ℕ) :
    (splitKummerModel p n).Points ≃
      {ix : Fin (p ^ n) × (AlgebraicClosure ℚ_[p])ˣ // ix.2 ^ (p ^ n) = 1} := by
  let e := (Bialgebra.restrictPoints ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])
    (SplitKummerCoordinate p n)).trans
      (KummerAlgebra.coordinateUnitPointsEquiv ℤ_[p] (p ^ n) 1
        (pow_pos (Fact.out : p.Prime).pos _))
  exact e.trans (Equiv.subtypeEquivRight fun x ↦ by simp)

/-- The model satisfies the actual finite-flat geometric-point predicate. -/
theorem splitKummer_isFiniteFlat (n : ℕ) :
    GaloisModule.IsFiniteFlat ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])
      (splitKummerModel p n).Points := (splitKummerModel p n).isFiniteFlat

end ThreeAdicPlan
