/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierTatePairing
public import FLT.GroupScheme.CartierDualCharacterGroup

/-! # Bilinearity of the original root-valued Tate pairing -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

omit [IsLocalRing R] in
/-- The actual finite Cartier pairing is additive in its dual point. -/
theorem FF.cartierPairing_add_left (X : FF R K)
    (y z : X.cartierDual.Points) (x : X.Points) :
    X.cartierPairing (y + z) x = X.cartierPairing y x * X.cartierPairing z x := by
  have he : X.dualPointCoordinate (y + z) = X.dualPointCoordinate y * X.dualPointCoordinate z := by
    unfold FF.dualPointCoordinate FF.pointCoordinate
    rw [map_add]
    exact BialgHom.algHom_mul_comp _ _ X.cartierDualGenericEquiv.symm.toBialgHom
  unfold FF.cartierPairing
  rw [he, HopfAlgebra.CartierDual.geometricCharactersEquiv_mul, MonoidHom.mul_apply]

omit [IsLocalRing R] in
/-- The zero dual point pairs to the actual unit. -/
@[simp] theorem FF.cartierPairing_zero_left (X : FF R K) (x : X.Points) :
    X.cartierPairing 0 x = 1 := by
  have h := X.cartierPairing_add_left 0 0 x
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

namespace PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- Addition in the original dual Tate module multiplies each original finite root. -/
theorem cartierTatePairing_add_left (y z : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    X.cartierTatePairing (y + z) x n =
      X.cartierTatePairing y x n * X.cartierTatePairing z x n := by
  unfold cartierTatePairing cartierTateLevelPairing
  rw [map_add]
  exact (X.level n).cartierPairing_add_left _ _ _

/-- Addition in the original Tate module multiplies each original finite root. -/
theorem cartierTatePairing_add_right (y : X.CartierTate) (x w : X.tateSequences) (n : ℕ) :
    X.cartierTatePairing y (x + w) n =
      X.cartierTatePairing y x n * X.cartierTatePairing y w n := by
  unfold cartierTatePairing cartierTateLevelPairing
  rw [map_add]
  exact (X.level n).cartierPairing_add_right _ _ _

/-- The original Tate pairing, with the multiplicative roots written additively. -/
def cartierTatePairingHom (n : ℕ) :
    X.CartierTate →+ (X.tateSequences →+ Additive (AlgebraicClosure K)ˣ) where
  toFun y :=
    { toFun := fun x ↦ Additive.ofMul (X.cartierTatePairing y x n)
      map_zero' := by
        change X.cartierTateLevelPairing n y (X.tateEval n 0) = 1
        rw [map_zero]
        exact (X.level n).cartierPairing_zero_right _
      map_add' := fun x w ↦ X.cartierTatePairing_add_right y x w n }
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    change X.cartierTateLevelPairing n 0 (X.tateEval n x) = 1
    unfold cartierTateLevelPairing
    rw [map_zero]
    exact (X.level n).cartierPairing_zero_left _
  map_add' y z := by
    apply AddMonoidHom.ext
    intro x
    exact X.cartierTatePairing_add_left y z x n

end PDivisibleSystem
end ThreeAdicPlan
