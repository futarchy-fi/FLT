/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FixedVector
public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Conditional propagation of Frobenius trace identities

This is leaf C3 of `docs/CHEBOTAREV_PLAN.md`. `PowerFrobCover` records the
arithmetic hypothesis that every image element is a conjugate of a power of
a chosen rational Frobenius. The rank-two trace identity propagates along
this cover using nonzero fixed vectors. The cover itself remains a hypothesis.

We spell out `Prime ℚ` as `HeightOneSpectrum (𝓞 ℚ)`. The representation's
endomorphisms carry their canonical module topology, as in `GaloisRep`;
over the finite discrete coefficient field this topology is discrete.
-/

@[expose] public section

open scoped NumberField
open IsDedekindDomain

namespace GaloisRepresentation.B5Inputs

/-- The chosen local arithmetic Frobenius mapped to the absolute Galois group
of `ℚ`, using the same algebraic-closure embedding as `GaloisRep.toLocal`. -/
noncomputable def QFrob (q : ℕ) (hq : q.Prime) : Field.absoluteGaloisGroup ℚ :=
  Field.absoluteGaloisGroup.map
    (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
    (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)

/-- Every image element is a conjugate of a nonnegative power of a chosen
rational Frobenius outside `S` and at a prime at least `N`. -/
def PowerFrobCover {M : Type*} [Monoid M] [TopologicalSpace M]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* M)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (N : ℕ) : Prop :=
  ∀ g, ∃ (q : ℕ) (hq : q.Prime), N ≤ q ∧
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S ∧
    ∃ (σ : Field.absoluteGaloisGroup ℚ) (n : ℕ),
      f g = f (σ * (QFrob q hq) ^ n * σ⁻¹)

/-- A power-Frobenius cover propagates the rank-two trace identity from
the specified rational Frobenius elements to every Galois element. -/
@[nolint unusedArguments]
theorem trace_identity_of_powerFrobCover
    {k V : Type*} [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2) (ρ : GaloisRep ℚ k V)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (N : ℕ)
    (hc : letI := moduleTopology k (Module.End k V); PowerFrobCover ρ S N)
    (hF : ∀ q (hq : q.Prime), N ≤ q →
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      (ρ (QFrob q hq)).trace k V = 1 + (ρ (QFrob q hq)).det) :
    ∀ g, (ρ g).trace k V = 1 + (ρ g).det := by
  intro g
  obtain ⟨q, hq, hN, hS, σ, n, hg⟩ := hc g
  change ρ g = ρ (σ * (QFrob q hq) ^ n * σ⁻¹) at hg
  rw [hg]
  apply (trace_eq_one_add_det_iff_fixedVector hV _).mpr
  exact fixedVector_conj_pow ρ.toRepresentation (QFrob q hq) σ n
    ((trace_eq_one_add_det_iff_fixedVector hV _).mp (hF q hq hN hS))

end GaloisRepresentation.B5Inputs
