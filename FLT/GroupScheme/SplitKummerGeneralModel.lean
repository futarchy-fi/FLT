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

/-! # Split Kummer levels over a characteristic-zero field

The equations are X^(p^n) = 1 on each of p^n components. The point comparison
here reads these equations; identifying the standard representation's tensor
quotient and its local action is a separate obligation.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan
variable (R K : Type) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (p : ℕ) [Fact p.Prime]

/-- The actual split Kummer coordinate algebra at level n. -/
abbrev GeneralSplitKummerCoordinate (n : ℕ) := KummerAlgebra.Coordinate R (p ^ n) 1

/-- The split Kummer model, with its actual geometric-point Galois action. -/
def generalSplitKummerModel (n : ℕ) : FF R K := by
  letI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let H := GeneralSplitKummerCoordinate R p n
  letI : HopfAlgebra.IsFiniteFlat R H :=
    KummerAlgebra.coordinate_isFiniteFlat R (p ^ n) 1 (pow_pos (Fact.out : p.Prime).pos _)
  letI : Algebra.Etale K (K ⊗[R] H) :=
    KummerAlgebra.generic_etale R (p ^ n) 1 (pow_pos (Fact.out : p.Prime).pos _)
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast pow_ne_zero n (Fact.out : p.Prime).ne_zero))
  letI := HopfAlgebra.pointsCommGroup K (AlgebraicClosure K) (K ⊗[R] H)
  exact
    { CoordinateRing := H
      Points := Additive (K ⊗[R] H →ₐ[K] AlgebraicClosure K)
      points :=
        { toFun := id
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      points_bijective := Function.bijective_id }

/-- Reading the component and root gives all geometric points of the actual model. -/
def generalSplitKummerCoordinates (n : ℕ) :
    (generalSplitKummerModel R K p n).Points ≃
      {ix : Fin (p ^ n) × (AlgebraicClosure K)ˣ // ix.2 ^ (p ^ n) = 1} := by
  let e := (Bialgebra.restrictPoints R K (AlgebraicClosure K)
    (GeneralSplitKummerCoordinate R p n)).trans
      (KummerAlgebra.coordinateUnitPointsEquiv R (p ^ n) 1
        (pow_pos (Fact.out : p.Prime).pos _))
  exact e.trans (Equiv.subtypeEquivRight fun x ↦ by simp)

/-- The model satisfies the actual finite-flat geometric-point predicate. -/
theorem generalSplitKummer_isFiniteFlat (n : ℕ) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K)
      (generalSplitKummerModel R K p n).Points := (generalSplitKummerModel R K p n).isFiniteFlat

end ThreeAdicPlan
