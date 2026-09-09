/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import FLT.FreyCurve.Basic
public import FLT.EllipticCurve.Torsion
public import FLT.MazurW
import FLT.GaloisRepresentation.HardlyRamified.Frey
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import FLT.Assumptions.KnownIn1980s
/-!

# Irreducibility of the p-torsion of the Frey curve

A deep result of Mazur implies that the Frey curve is irreducible.

-/

@[expose] public section

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

/-- The exact missing bridge between reducibility of the Frey representation
and the forbidden torsion configuration in `mazur_W`.

This packages the ch03 character analysis, the finite-flat/Tate local input,
the triviality of the resulting global character, and the quotient/dual-isogeny
construction.  Isolating this statement prevents `FreyPackage.mazur` from
hiding the whole implication behind an unrestricted `knownin1980s` proof. -/
theorem FreyPackage.mazurW_counterexample_of_reducible (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (E.galoisRep p P.hppos) →
      ∃ (E' : WeierstrassCurve ℚ) (hE' : E'.IsElliptic),
        letI : E'.IsElliptic := hE'
        ∃ f : ((ZMod 2 × ZMod 2) × ZMod p) →+ (E'⁄ℚ).Point,
          Function.Injective f := by
  -- Serre, Duke Math. J. 54 (1987), §4.1 (the exact proposition locator is
  -- still tracked as cartography question PQ5), together with the steps above.
  knownin1980s

/--
For exponent at least `17`, the p-torsion in the Frey curve associated to a
counterexample to FLT is irreducible.
-/
theorem FreyPackage.mazur (P : FreyPackage) (hp17 : 17 ≤ P.p) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) := by
  by_contra hred
  obtain ⟨E', hE', f, hf⟩ := P.mazurW_counterexample_of_reducible hred
  let : E'.IsElliptic := hE'
  exact mazur_W P.p P.pp hp17 E' ⟨f, hf⟩
