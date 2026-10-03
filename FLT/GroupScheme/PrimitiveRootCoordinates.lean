/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Additive coordinates on roots of unity

A primitive root gives actual additive coordinates, including the action
of power maps. No Galois action or choice of compatible roots is assumed.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {L : Type*} [Field L] {m : ℕ} [NeZero m]

/-- A primitive root identifies roots of unity with additive residues. -/
def primitiveRootCoordinates {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ m) :
    ZMod m ≃+ Additive (rootsOfUnity m L) :=
  hζ.zmodEquivZPowers.trans
    (MulEquiv.subgroupCongr hζ.zpowers_eq).toAdditive

/-- Residue coordinates exponentiate the chosen primitive root. -/
theorem primitiveRootCoordinates_val {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ m) (a : ZMod m) :
    ((primitiveRootCoordinates hζ a).toMul : Lˣ) = ζ ^ a.val := by
  change ((hζ.zmodEquivZPowers a).toMul : Lˣ) = _
  conv_lhs => rw [← ZMod.natCast_zmod_val a, hζ.zmodEquivZPowers_apply_coe_nat]
  rfl

/-- Raising a root to a natural power multiplies its additive coordinate. -/
theorem primitiveRootCoordinates_pow {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ m)
    (a : ZMod m) (k : ℕ) :
    primitiveRootCoordinates hζ ((k : ZMod m) * a) =
      Additive.ofMul ((primitiveRootCoordinates hζ a).toMul ^ k) := by
  rw [← nsmul_eq_mul, map_nsmul]
  rfl

/-- A characteristic-zero algebraic closure has a primitive root at every nonzero level. -/
def algebraicClosurePrimitiveRoot (K : Type*) [Field K] [CharZero K] (m : ℕ) [NeZero m] :
    (AlgebraicClosure K)ˣ :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) m).choose_spec.isUnit
    (NeZero.ne m) |>.unit

/-- The chosen unit is a primitive root of the specified order. -/
theorem algebraicClosurePrimitiveRoot_spec (K : Type*) [Field K] [CharZero K]
    (m : ℕ) [NeZero m] : IsPrimitiveRoot (algebraicClosurePrimitiveRoot K m) m :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) m).choose_spec.isUnit_unit
    (NeZero.ne m)

end ThreeAdicPlan
