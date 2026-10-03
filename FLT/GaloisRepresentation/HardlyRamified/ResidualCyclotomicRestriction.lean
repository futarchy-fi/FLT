/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.FiniteFlatCyclotomicAbsolute
public import FLT.GaloisRepresentation.HardlyRamified.AbsoluteIrreducibility
public import FLT.GaloisRepresentation.HardlyRamified.ModThreeProved
public import FLT.GaloisRepresentation.HardlyRamified.ResidualCyclotomicDeterminant

/-!
# Cyclotomic restriction of irreducible residual HR representations

Hardly ramifiedness supplies flatness, the actual determinant and oddness.
Proved mod-three reducibility excludes p = 3. Residual irreducibility is
still required; the family theorem does not assume it.
-/

@[expose] public noncomputable section
universe u

namespace GaloisRepresentation.IsHardlyRamified

/-- Every irreducible finite residual HR representation stays absolutely irreducible
on the cyclotomic kernel. The mod-three theorem excludes the small odd prime. -/
theorem residual_cyclotomic_restriction_absolute
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {k V : Type} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified hpodd hV ρ) (hirr : ρ.IsIrreducible) :
    Representation.IsAbsolutelyIrreducible.{u}
      (ρ.toRepresentation.comp (CyclotomicQuadratic.character p).ker.subtype) := by
  have hp : 3 < p := by
    have htwo := (Fact.out : p.Prime).two_le
    have hne : p ≠ 3 := by
      rintro rfl
      exact not_isIrreducible_three hV hρ hirr
    obtain ⟨n, hn⟩ := hpodd
    omega
  let : CharP k p := ThreeAdicPlan.charP_of_finite_padic_algebra p k
  have hv : LocalCyclotomic.rationalPlace p =
      (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat := by
    ext x
    change x ∈ (Ideal.span {(p : ℤ)}).map
      (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)).symm ↔
      Rat.ringOfIntegersEquiv x ∈ Ideal.span {(p : ℤ)}
    rw [Ideal.map_symm]
    change Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ) x ∈
      Ideal.span {(p : ℤ)} ↔ Rat.ringOfIntegersEquiv x ∈ Ideal.span {(p : ℤ)}
    rw [Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv]
  exact ρ.flat_cyclotomic_restriction_absolute_of_isFlatAt p hp (hv.symm ▸ hρ.isFlat)
    (Module.finrank_eq_of_rank_eq hV) (det_eq_modularCyclotomic hpodd hV hρ)
    (isAbsolutelyIrreducible hpodd hV hρ hirr)

end GaloisRepresentation.IsHardlyRamified
