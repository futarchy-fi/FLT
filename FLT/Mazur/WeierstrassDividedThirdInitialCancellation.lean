/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdInitialResidualAlgebra

/-!
# Third-layer cancellation on the actual corrected depth-one initial edge

The installed initial open is used on the left, and the original retained
right puncture on the right. Their remaining parameter is the entire original
Mobius/right composite, with no fixed-parameter identification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdInitialAtlasChart arithmeticThirdAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- The entire initial residual reduces to its original full base parameter at stage three. -/
theorem arithmeticThirdInitialResidual_third (b : Bool) :
    arithmeticThirdInitialResidual hπ data H 3 j hj u hu b =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 3 j hj)).hom := by
  rw [← arithmeticThirdInitialEquiv_spec, arithmeticThirdInitialEquiv_third]

variable [IsBezout R] (ha : 1 = j)
local notation "ι" => arithmeticThirdInitialAtlasChart hπ data H 3 j hj u hu
local notation "J" => arithmeticThirdInitialIdentification hπ data H 3 j hj u hu ha
local notation "M" => arithmeticThirdPrecedingIdentification hπ data H 3 j hj u hu 0 ha
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu 3

/-- The actual depth-one edge cancels at layer three while retaining its original parameter. -/
@[reassoc] theorem arithmeticThirdInitialAtlas_initial_third (b : Bool) :
    arithmeticThirdInitialPuncture hπ data H 3 j hj u hu b ≫ (J b).hom ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 3 j hj)).hom ≫
        rightBranchOpen (Quotient R π 3) (s b) ≫ (M b).hom ≫
          ι (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  rw [arithmeticThirdInitialAtlas_residual_initial, arithmeticThirdInitialResidual_third]

end FLT.Mazur.WeierstrassDividedDepth
