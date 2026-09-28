/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import FLT.MazurChapter.AdmissibleGroupSchemes

/-! # Axiom checks for the elementary prime-order group schemes

The elementary models and their orders must not depend on the admitted classification.
-/

/-- info: 'FLT.MazurChapter.multiplicativeOrderPrime'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.MazurChapter.multiplicativeOrderPrime

/-- info: 'FLT.MazurChapter.multiplicativeOrderPrime_order'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.MazurChapter.multiplicativeOrderPrime_order

/-- info: 'FLT.MazurChapter.constantOrderPrime'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.MazurChapter.constantOrderPrime

/-- info: 'FLT.MazurChapter.constantOrderPrimeCoordinateEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.MazurChapter.constantOrderPrimeCoordinateEquiv

/-- info: 'FLT.MazurChapter.constantOrderPrime_order'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FLT.MazurChapter.constantOrderPrime_order

open scoped TensorProduct
open FLT.MazurChapter

-- The counit evaluates at the identity of the constant group.
example (p : ℕ) [NeZero p] (hp : p.Prime)
    (f : HopfAlgebra.CartierDual ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod p)))) :
    Coalgebra.counit (R := ℤ) f = constantOrderPrimeCoordinateEquiv p hp f 1 := rfl

-- Comultiplication is pullback along the group law, rather than diagonal multiplication.
example (p : ℕ) [NeZero p] (hp : p.Prime)
    (f : HopfAlgebra.CartierDual ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod p))))
    (a b : Multiplicative (ZMod p)) :
    HopfAlgebra.CartierDual.tensorEquiv ℤ
      (MonoidAlgebra ℤ (Multiplicative (ZMod p)))
      (MonoidAlgebra ℤ (Multiplicative (ZMod p)))
      (Coalgebra.comul (R := ℤ) f)
      (MonoidAlgebra.single a 1 ⊗ₜ MonoidAlgebra.single b 1) =
        constantOrderPrimeCoordinateEquiv p hp f (a * b) := by
  change HopfAlgebra.CartierDual.tensorEquiv ℤ _ _
    (HopfAlgebra.CartierDual.comul f) _ = f (MonoidAlgebra.single (a * b) 1)
  rw [HopfAlgebra.CartierDual.comul_eval, MonoidAlgebra.single_mul_single, one_mul]
