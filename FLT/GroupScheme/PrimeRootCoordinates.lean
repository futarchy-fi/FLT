/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerCoefficients
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Prime-field coordinates on roots of unity

A chosen primitive root identifies the additive prime field with the root
coefficient group. The field containing the roots need not have characteristic p.
-/

@[expose] public section

namespace KummerTheory

variable {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)

/-- Coordinates obtained by taking powers of the chosen primitive root. -/
noncomputable def primeRootCoordinates : ZMod p ≃+ RootModule L p :=
  hζ.zmodEquivZPowers.trans (MulEquiv.subgroupCongr hζ.zpowers_eq).toAdditive

/-- Natural-integer coordinates correspond to ordinary powers. -/
@[simp] theorem rootUnit_primeRootCoordinates_nat (m : ℕ) :
    rootUnit (primeRootCoordinates hζ (m : ZMod p)) = ζ ^ m := by
  change (hζ.zmodEquivZPowers (m : ZMod p)).toMul.val = ζ ^ m
  rw [hζ.zmodEquivZPowers_apply_coe_nat]
  rfl

/-- Every prime-field coordinate has the expected root value. -/
theorem rootUnit_primeRootCoordinates (x : ZMod p) :
    rootUnit (primeRootCoordinates hζ x) = ζ ^ x.val := by
  simpa only [ZMod.natCast_zmod_val] using rootUnit_primeRootCoordinates_nat hζ x.val

/-- Multiplication of coordinates is natural scaling of root coefficients. -/
theorem primeRootCoordinates_mul (a x : ZMod p) :
    primeRootCoordinates hζ (a * x) = a.val • primeRootCoordinates hζ x := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

end KummerTheory
