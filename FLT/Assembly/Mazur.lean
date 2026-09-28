/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Mazur
public import FLT.MazurWOfPrimeTorsion

/-!
# The rational torsion input to the FLT assembly

Only the exclusion of the indicated torsion configuration is needed. The
reducible Frey representation already constructs precisely that configuration.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace FLT.Assembly

/-- Rational elliptic curves exclude full two-torsion together with large prime torsion. -/
def MazurTorsionExclusion : Prop :=
  ∀ (p : ℕ), p.Prime → 17 ≤ p →
    ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
      ¬ ∃ f : ((ZMod 2 × ZMod 2) × ZMod p) →+ (E⁄ℚ).Point,
        Function.Injective f

/-- Excluding prime-order points supplies the torsion configuration exclusion. -/
theorem mazurTorsionExclusion_of_noLargePrimeTorsion
    (h : NoLargePrimeTorsion) : MazurTorsionExclusion := by
  intro p hp hp17 E hE
  let instElliptic : E.IsElliptic := hE
  exact mazur_W_of_noLargePrimeTorsion h p hp hp17 E

end FLT.Assembly

/-- The explicit rational torsion exclusion makes the Frey representation irreducible. -/
theorem FreyPackage.mazur_of_torsionExclusion
    (hmazur : FLT.Assembly.MazurTorsionExclusion)
    (P : FreyPackage) (hp17 : 17 ≤ P.p) :
    have _instPrime : Fact P.p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) := by
  let instPrime : Fact P.p.Prime := ⟨P.pp⟩
  by_contra hred
  obtain ⟨E, hE, f, hf⟩ := P.mazurW_counterexample_of_reducible hred
  exact hmazur P.p P.pp hp17 E hE ⟨f, hf⟩
