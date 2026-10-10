/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# An elementary bound for points over a small finite field

Every nonsingular point is either infinity or has two coordinates in the field.
The resulting bound q² + 1 suffices at q = 2 and q = 3 for primes at least 17,
and applies equally to smooth and singular special cubics.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The affine point type embeds in infinity together with pairs of coordinates. -/
def affinePointCoordinates : W.toAffine.Point ↪ Option (F × F) where
  toFun
    | .zero => none
    | .some x y _ => some (x, y)
  inj' := by
    rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) he
    · rfl
    · cases he
    · cases he
    · have hh : x = x' ∧ y = y' := by simpa only [Option.some.injEq, Prod.mk.injEq] using he
      rcases hh with ⟨rfl, rfl⟩
      rfl

/-- Finite residue fields give finite nonsingular point groups, including singular cubics. -/
theorem finite_affinePoints_of_finite [Finite F] : Finite W.toAffine.Point :=
  Finite.of_injective (affinePointCoordinates W) (affinePointCoordinates W).injective

/-- Counting coordinate pairs bounds the full nonsingular point group by q² + 1. -/
theorem card_affinePoints_le_square_add_one [Finite F] :
    Nat.card W.toAffine.Point ≤ Nat.card F ^ 2 + 1 := by
  classical
  let _ := Fintype.ofFinite F
  have h := Nat.card_le_card_of_injective _ (affinePointCoordinates W).injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_prod, pow_two] using h

end FLT.Mazur
