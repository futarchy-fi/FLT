/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AtTwo
public import FLT.GaloisRepresentation.HardlyRamified.PrimeField
public import FLT.FreyCurve.Basic
public import FLT.FreyCurve.Serre.Unramified
public import FLT.EllipticCurve.Torsion
public import FLT.EllipticCurve.WeilPairingDeterminant
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The Frey curve gives a hardly ramified representation

We prove that the `ℓ`-torsion of the Frey curve attached to a Frey package
is a hardly ramified Galois representation, and deduce that this representation is
not irreducible from the generic prime-field theorem. The determinant and flatness
fields remain separate arithmetic inputs.
-/

@[expose] public section

variable (P : FreyPackage)

open GaloisRepresentation

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- We cannot hope to make a constructive decidable equality on `AlgebraicClosure ℚ` because
it is defined in a completely nonconstructive way, so we add the classical instance. -/
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

/-- The `p`-torsion of the Frey curve has rank two over `ZMod p`. -/
theorem FreyCurve.torsion_rank :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    Module.rank (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) = 2 := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  obtain ⟨e⟩ := (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).n_torsion_dimension
    (n := P.p) (by exact_mod_cast (Nat.ne_of_gt P.hppos))
  let e' : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p ≃ₗ[ZMod P.p]
      ZMod P.p × ZMod P.p :=
    { e with map_smul' := ZMod.map_smul e }
  rw [e'.rank_eq, rank_prod]
  simp only [Module.rank_self, Cardinal.lift_one]
  exact one_add_one_eq_two

/-- A checked Weil pairing on Frey torsion supplies exactly the determinant field of
`IsHardlyRamified`. Constructing this pairing is still required. -/
theorem FreyCurve.torsion_det_of_weilPairing :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ (_w : P.freyCurve.TorsionWeilPairing P.p) g,
      (P.freyCurve.galoisRep P.p P.hppos).det g =
        algebraMap ℤ_[P.p] (ZMod P.p)
          (cyclotomicCharacter (AlgebraicClosure ℚ) P.p g.toRingEquiv) := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  intro w g
  exact w.det_galoisRep P.hppos g

/-- The determinant of Frey torsion is the cyclotomic character, as required by
`IsHardlyRamified.det`. This input requires the nondegenerate, Galois-equivariant
Weil pairing and its determinant comparison. -/
theorem FreyCurve.torsion_det :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ g, (P.freyCurve.galoisRep P.p P.hppos).det g =
      algebraMap ℤ_[P.p] (ZMod P.p)
        (cyclotomicCharacter (AlgebraicClosure ℚ) P.p g.toRingEquiv) :=
  sorry

/-- Frey torsion is flat at its residual prime, as required by
`IsHardlyRamified.isFlat`, including the condition for every open coefficient ideal.
Both good and multiplicative reduction at that prime must be treated. -/
theorem FreyCurve.torsion_isFlat :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : P.p.Prime)) :=
  sorry

/-- Assemble the rank, determinant, unramifiedness, flatness, and quotient-at-two
inputs for Frey torsion. -/
theorem FreyCurve.torsion_isHardlyRamified :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    IsHardlyRamified P.hp_odd (FreyCurve.torsion_rank P)
      (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  exact {
    det := FreyCurve.torsion_det P
    isUnramified := fun _ hq hq' ↦ FreyCurve.torsion_isUnramifiedAt P hq hq'.1 hq'.2
    isFlat := FreyCurve.torsion_isFlat P
    isTameAtTwo := FreyCurve.torsion_quotient_at_two P }

/-- The generic prime-field reducibility theorem applies to Frey torsion because
its exponent is at least five and it is hardly ramified. -/
theorem FreyCurve.torsion_not_isIrreducible :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) := by
  let : Fact P.p.Prime := ⟨P.pp⟩
  exact IsHardlyRamified.not_isIrreducible_of_prime_field P.p P.hp5 P.hp_odd _
    (FreyCurve.torsion_rank P) (P.freyCurve.galoisRep P.p P.hppos)
    (FreyCurve.torsion_isHardlyRamified P)
