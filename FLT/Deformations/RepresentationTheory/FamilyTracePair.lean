/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.RepresentationTheory.TraceCompatiblePair
public import FLT.GaloisRepresentation.HardlyRamified.B5Inputs

/-!
# Common traces from a compatible family

The coefficient of `X` in the common quadratic Frobenius polynomial gives
trace compatibility between any two members of a compatible family.
-/

@[expose] public section

namespace GaloisRepresentation

open scoped NumberField

/-- Arithmetic Frobenius trace at a rational prime, extended by zero elsewhere. -/
noncomputable def frobTrace {R V : Type*} [CommRing R] [TopologicalSpace R]
    [AddCommGroup V] [Module R V] (ρ : GaloisRep ℚ R V) (q : ℕ) : R :=
  if hq : q.Prime then
    (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob
        hq.toHeightOneSpectrumRingOfIntegersRat)).trace R V
  else 0

/-- Two members of a compatible family have common trace coefficients away
from the exceptional set and their residue characteristics. -/
theorem traceCompatiblePair_of_isCompatible {E : Type*} [Field E] [NumberField E]
    {ℓ p : ℕ} (σ : GaloisRepFamily ℚ E 2) (hσ : σ.isCompatible)
    (hℓ : Fact ℓ.Prime) (φ : E →+* AlgebraicClosure ℚ_[ℓ])
    (hp : Fact p.Prime) (ψ : E →+* AlgebraicClosure ℚ_[p]) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
      TraceCompatiblePair φ ψ
        (fun q ↦ ∃ hq : q.Prime, 5 ≤ q ∧ q ≠ ℓ ∧ q ≠ p ∧
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ S)
        (frobTrace (σ hℓ φ)) (frobTrace (σ hp ψ)) := by
  classical
  obtain ⟨S, P, hP⟩ := hσ
  refine ⟨S, (fun q ↦ if hq : q.Prime then
    -(P hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 else 0), ?_⟩
  intro q hqgood
  obtain ⟨hq, _, hqℓ, hqp, hqS⟩ := hqgood
  have hleft := (hP hℓ φ _ hqS (B5Inputs.prime_not_mem hℓ.out hq hqℓ)).2
  have hright := (hP hp ψ _ hqS (B5Inputs.prime_not_mem hp.out hq hqp)).2
  simp only [frobTrace, dite_eq_left hq]
  constructor
  · rw [B5Inputs.trace_eq_neg_coeff, hleft, Polynomial.coeff_map, map_neg]
  · rw [B5Inputs.trace_eq_neg_coeff, hright, Polynomial.coeff_map, map_neg]

end GaloisRepresentation
