/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Assembly.Proof
public import Mathlib.Topology.Instances.ZMod

/-!
# Conditional assembly from residual Frey traces

Cofinitely many Frobenius trace identities for irreducible Frey torsion suffice
for Fermat's Last Theorem, with rational torsion exclusion as a separate premise.
-/

@[expose] public section

open GaloisRepresentation
open scoped NumberField

namespace FLT.Assembly

/-- The trace is `1 + q` away from finitely many places and the residual prime. -/
def CofiniteFrobeniusTrace {R V : Type} [CommRing R] [TopologicalSpace R]
    [AddCommGroup V] [Module R V] (p : ℕ) (ρ : GaloisRep ℚ R V) : Prop :=
  ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
    ∀ q (hq : q.Prime), 5 ≤ q → q ≠ p →
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).trace R V = 1 + q

/-- The residual trace input needed only for irreducible Frey representations
with exponent at least seventeen. -/
def FreyResidualTraceInput : Prop :=
  ∀ P : FreyPackage, 17 ≤ P.p →
    letI : Fact P.p.Prime := ⟨P.pp⟩
    let ρ := P.freyCurve.galoisRep P.p P.hppos
    ρ.IsIrreducible → CofiniteFrobeniusTrace P.p ρ

/-- The natural p-adic algebra structure on the prime field. -/
noncomputable local instance freyTracePrimeFieldPadicAlgebra (p : ℕ) [Fact p.Prime] :
    Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- Residual Frobenius traces imply reducibility of Frey torsion. -/
theorem B4_of_freyResidualTrace (htrace : FreyResidualTraceInput) : FLT.Bosses.B4 := by
  intro P hp17
  let instPrime : Fact P.p.Prime := ⟨P.pp⟩
  let instLocalHom : IsLocalHom (algebraMap ℤ_[P.p] (ZMod P.p)) :=
    IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _)
  change ¬ (P.freyCurve.galoisRep P.p P.hppos).IsIrreducible
  intro hirr
  obtain ⟨S, hS⟩ := htrace P hp17 hirr
  exact B5Inputs.not_isIrreducible_of_frobenius_traces P.p P.hp5
    (FreyCurve.torsion_rank P) (P.freyCurve.galoisRep P.p P.hppos)
    (FreyCurve.torsion_det P) S hS hirr

/-- Rational torsion exclusion and the residual trace input imply FLT. -/
theorem flt_of_freyResidualTrace (hmazur : MazurTorsionExclusion)
    (htrace : FreyResidualTraceInput) : FermatLastTheorem :=
  FLT.Bosses.B2_implies_B1 (FLT.Bosses.B3_implies_B2
    (FLT.Bosses.B3_of_torsionExclusion hmazur (B4_of_freyResidualTrace htrace)))

end FLT.Assembly

/-- The positive-natural form of FLT from rational torsion exclusion and
cofinite residual Frey traces. -/
theorem PNat.pow_add_pow_ne_pow_of_freyResidualTrace
    (hmazur : FLT.Assembly.MazurTorsionExclusion)
    (htrace : FLT.Assembly.FreyResidualTraceInput)
    (x y z : ℕ+) (n : ℕ) (hn : n > 2) : x ^ n + y ^ n ≠ z ^ n :=
  PNat.pow_add_pow_ne_pow_of_FermatLastTheorem
    (FLT.Assembly.flt_of_freyResidualTrace hmazur htrace) x y z n hn
