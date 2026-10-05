/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.TateRootModule
public import FLT.GroupScheme.PDivisibleCartierTateGalois

/-! # The actual finite Cartier pairing as a p-adic bilinear map into roots -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- The finite pairing lands in roots of its actual annihilating order. -/
def finiteRootPairingHom (n : ℕ) :
    (X.cartierDual.level n).Points →+
      ((X.level n).Points →+ TateRootLevel (AlgebraicClosure K) p n) where
  toFun y :=
    { toFun x := Additive.ofMul ⟨(X.level n).cartierPairing y x,
        (X.level n).cartierPairing_pow_eq_one y x _ (X.killed n x)⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact (X.level n).cartierPairing_zero_right y
      map_add' x z := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact (X.level n).cartierPairing_add_right y x z }
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    have he := (X.level n).cartierPairing_add_left 0 0 x
    rw [add_zero] at he
    exact mul_eq_left.mp he.symm
  map_add' y z := by
    apply AddMonoidHom.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (X.level n).cartierPairing_add_left y z x

/-- The original finite pairing is linear in its original point argument. -/
def finiteRootPairingRight (n : ℕ) (y : (X.cartierDual.level n).Points) :
    (X.level n).Points →ₗ[ℤ_[p]] TateRootLevel (AlgebraicClosure K) p n where
  __ := X.finiteRootPairingHom n y
  map_smul' a x := by
    change X.finiteRootPairingHom n y (PadicInt.toZModPow n a • x) =
      PadicInt.toZModPow n a • X.finiteRootPairingHom n y x
    exact ZMod.map_smul (X.finiteRootPairingHom n y) _ x

/-- The finite Cartier pairing is bilinear with the same actual p-adic residue action. -/
def finiteRootPairing (n : ℕ) :
    (X.cartierDual.level n).Points →ₗ[ℤ_[p]]
      ((X.level n).Points →ₗ[ℤ_[p]] TateRootLevel (AlgebraicClosure K) p n) where
  toFun := X.finiteRootPairingRight n
  map_add' y z := by
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun ((X.finiteRootPairingHom n).map_add y z) x
  map_smul' a y := by
    apply LinearMap.ext
    intro x
    let f : (X.cartierDual.level n).Points →+ TateRootLevel (AlgebraicClosure K) p n :=
      { toFun z := X.finiteRootPairingHom n z x
        map_zero' := DFunLike.congr_fun ((X.finiteRootPairingHom n).map_zero) x
        map_add' z w := DFunLike.congr_fun ((X.finiteRootPairingHom n).map_add z w) x }
    change f (PadicInt.toZModPow n a • y) = PadicInt.toZModPow n a • f y
    exact ZMod.map_smul f _ y

/-- Forgetting the finite-root subtype gives exactly the original Cartier unit. -/
theorem finiteRootPairing_value (n : ℕ) (y : (X.cartierDual.level n).Points)
    (x : (X.level n).Points) :
    tateRootValue (AlgebraicClosure K) p n (X.finiteRootPairing n y x) =
      Additive.ofMul ((X.level n).cartierPairing y x) := rfl
end ThreeAdicPlan.PDivisibleSystem
