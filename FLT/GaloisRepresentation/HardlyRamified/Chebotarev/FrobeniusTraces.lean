/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.WeakChebotarev
public import FLT.GaloisRepresentation.HardlyRamified.TraceReducibility
public import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

import FLT.DedekindDomain.AdicValuation
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Topology.Algebra.Group.Units

/-!
# Frobenius traces and reducibility

The cyclotomic Frobenius formula and the unconditional power-Frobenius cover
propagate the rank-two fixed-vector property to every Galois element.
This proves the B5 trace criterion without the full Chebotarev density theorem.
The finite-group reduction and the cyclotomic special case of full density
are retained as independent results.
-/

@[expose] public section

open scoped NumberField
open IsDedekindDomain

namespace GaloisRepresentation.B5Inputs

section FrobeniusTraces

-- Match the completion structures used when `GaloisRep.toLocal` was defined.
-- Otherwise the arbitrary algebraic-closure lifts need not agree definitionally.
attribute [local instance 2000] HeightOneSpectrum.adicCompletion.instField
  HeightOneSpectrum.instAlgebraAdicCompletion

universe u

/-- The finite-monoid Chebotarev statement follows from its surjective
finite-group case. Lift the map to units and restrict its codomain to its
image subgroup, with the inherited finite discrete topology. The resulting
map is continuous and surjective; applying the inclusion to the Frobenius
equality recovers the original statement. No density theorem is used here. -/
@[nolint unusedArguments]
theorem chebotarev_frobenius_dense_of_surjective_group_case
    {M : Type u} [Monoid M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* M)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (N : ℕ)
    (g : Field.absoluteGaloisGroup ℚ)
    (hgroup : ∀ {G : Type u} [Group G] [Finite G]
      [TopologicalSpace G] [DiscreteTopology G]
      (f : Field.absoluteGaloisGroup ℚ →ₜ* G), Function.Surjective f →
      ∃ (q : ℕ) (hq : q.Prime), N ≤ q ∧
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S ∧
      ∃ σ : Field.absoluteGaloisGroup ℚ,
        f g = f (σ * Field.absoluteGaloisGroup.map
          (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
          (Field.AbsoluteGaloisGroup.adicArithFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) * σ⁻¹)) :
    ∃ (q : ℕ) (hq : q.Prime), N ≤ q ∧
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S ∧
      ∃ σ : Field.absoluteGaloisGroup ℚ,
        f g = f (σ * Field.absoluteGaloisGroup.map
          (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
          (Field.AbsoluteGaloisGroup.adicArithFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) * σ⁻¹) := by
  let u := f.toMonoidHom.toHomUnits
  have hu : Continuous u := Units.continuous_iff.mpr
    ⟨f.continuous, f.continuous.comp continuous_inv⟩
  let π : Field.absoluteGaloisGroup ℚ →ₜ* u.range :=
    { u.rangeRestrict with continuous_toFun := hu.subtype_mk _ }
  let ι : u.range →* M := (Units.coeHom M).comp u.range.subtype
  obtain ⟨q, hq, hN, hS, σ, hσ⟩ := hgroup π u.rangeRestrict_surjective
  exact ⟨q, hq, hN, hS, σ, congrArg ι hσ⟩

/-- The residue field of the completion of ℚ at `q` has `q` elements. -/
private theorem adicCompletion_residueField_card (q : ℕ) (hq : q.Prime) :
    Nat.card (IsLocalRing.ResidueField
      (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ)) = q := by
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let e : (𝓞 ℚ) ⧸ v.asIdeal ≃+* ZMod q :=
    (Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv (by
      change Ideal.span {(q : ℤ)} =
        Ideal.map Rat.ringOfIntegersEquiv.toRingHom
          (Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(q : ℤ)}))
      exact (Ideal.map_comap_of_surjective Rat.ringOfIntegersEquiv.toRingHom
        Rat.ringOfIntegersEquiv.surjective _).symm)).trans
      (Int.quotientSpanNatEquivZMod q)
  rw [← Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField ℚ v).toEquiv,
    Nat.card_congr e.toEquiv, Nat.card_zmod]

open IsLocalRing in
set_option backward.isDefEq.respectTransparency false in
/-- Arithmetic Frobenius acts by the `q`th power on roots of unity of order
coprime to `q` in the algebraic closure of the completion at `q`. -/
private theorem adicArithFrob_apply_of_pow_eq_one
    (n q : ℕ) (hnpos : 0 < n) (hq : q.Prime) (hcop : Nat.Coprime q n)
    (ζ : AlgebraicClosure (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
    (hζ : ζ ^ n = 1) :
    Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat ζ = ζ ^ q := by
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let S := IntegralClosure R (AlgebraicClosure K)
  let Q := maximalIdeal S
  have hQR : Q.under R = maximalIdeal R :=
    maximalIdeal_comap (algebraMap R S)
  have hc : Nat.card (R ⧸ Q.under R) = q := by
    rw [hQR]
    exact adicCompletion_residueField_card q hq
  have hn : (n : S) ∉ Q := by
    have hqS : (q : S) ∈ Q := by
      have hqR : (q : R) ∈ maximalIdeal R := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        rw [map_natCast, ← adicCompletion_residueField_card q hq]
        let := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers ℚ))
        simpa only [Nat.card_eq_fintype_card] using
          Nat.cast_card_eq_zero (ResidueField (v.adicCompletionIntegers ℚ))
      rw [← map_natCast (algebraMap R S)]
      exact (show (q : R) ∈ Q.under R from hQR ▸ hqR)
    exact Ideal.IsPrime.notMem_of_isCoprime_of_mem
      (by simpa only [map_natCast] using hcop.isCoprime.map (Int.castRingHom S)) hqS
  let z : S := ⟨ζ, IsIntegral.of_pow hnpos (hζ ▸ isIntegral_one)⟩
  have hz : z ^ n = 1 := Subtype.ext hζ
  have H := (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob v).apply_of_pow_eq_one hz hn
  rw [hc] at H
  exact congrArg (algebraMap S (AlgebraicClosure K)) H

/-- At a rational prime `q ≠ p`, the `p`-adic cyclotomic character sends an
arithmetic Frobenius to `q`. This is independent of the chosen Frobenius lift
and embedding: inertia acts trivially on roots of unity of order prime to `q`,
and arithmetic Frobenius acts by the `q`th power on their reductions.

The local root-of-unity formula is transported through the chosen embedding
of algebraic closures. The character is then determined by its reductions
modulo every power of `p`. -/
@[nolint unusedArguments]
theorem cyclotomicCharacter_adicArithFrob
    (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) :
    (cyclotomicCharacter (AlgebraicClosure ℚ) p
      (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv : ℤ_[p]) = q := by
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let f := algebraMap ℚ (v.adicCompletion ℚ)
  let σ := Field.AbsoluteGaloisGroup.adicArithFrob v
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : AlgebraicClosure ℚ) ^ (p ^ n) = 1 := by
    exact congrArg Units.val ((mem_rootsOfUnity (p ^ n) t).mp ht)
  have hlocal := adicArithFrob_apply_of_pow_eq_one (p ^ n) q
    (pow_pos (Fact.out : p.Prime).pos n) hq
    ((hq.coprime_iff_not_dvd.mpr (fun h ↦
      hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h))).pow_right n)
    (AlgebraicClosure.map f t)
    (by rw [← map_pow, ht', map_one])
  have hglobal : Field.absoluteGaloisGroup.map f σ t = (t : AlgebraicClosure ℚ) ^ q := by
    apply (AlgebraicClosure.map f).injective
    rw [Field.absoluteGaloisGroup.lift_map, map_pow]
    exact hlocal
  change Field.absoluteGaloisGroup.map f σ t = _
  rw [hglobal, ZMod.val_natCast]
  exact pow_eq_pow_mod q ht'

/-- At a prime `q` coprime to `n`, the mod-`n` cyclotomic character sends
arithmetic Frobenius to the residue class of `q`. -/
theorem modularCyclotomicCharacter_adicArithFrob
    (n q : ℕ) [NeZero n] (hq : q.Prime) (hcop : Nat.Coprime q n) :
    (modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) n)
      (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv : ZMod n) = q := by
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let f := algebraMap ℚ (v.adicCompletion ℚ)
  let σ := Field.AbsoluteGaloisGroup.adicArithFrob v
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : AlgebraicClosure ℚ) ^ n = 1 :=
    congrArg Units.val ((mem_rootsOfUnity n t).mp ht)
  have hlocal := adicArithFrob_apply_of_pow_eq_one n q (NeZero.pos n) hq hcop
    (AlgebraicClosure.map f t) (by rw [← map_pow, ht', map_one])
  have hglobal : Field.absoluteGaloisGroup.map f σ t = (t : AlgebraicClosure ℚ) ^ q := by
    apply (AlgebraicClosure.map f).injective
    rw [Field.absoluteGaloisGroup.lift_map, map_pow]
    exact hlocal
  change Field.absoluteGaloisGroup.map f σ t = _
  rw [hglobal, ZMod.val_natCast]
  exact pow_eq_pow_mod q ht'

/-- Chebotarev for maps factoring through a finite cyclotomic character.
Dirichlet supplies arbitrarily large primes in the prescribed unit residue class.
Bounding the residue-field sizes also excludes the finite exceptional set.
The Frobenius image itself agrees with `f g`, so the conjugating element is `1`.
This proof uses only Dirichlet and the cyclotomic Frobenius formula. -/
@[nolint unusedArguments]
theorem chebotarev_frobenius_dense_of_factors_cyclotomic
    {M : Type*} [Monoid M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* M)
    (hfactor : ∃ n : ℕ, ∃ hn : 0 < n,
      letI : NeZero n := ⟨hn.ne'⟩
      ∃ φ : (ZMod n)ˣ → M, ∀ g : Field.absoluteGaloisGroup ℚ,
        f g = φ (modularCyclotomicCharacter (AlgebraicClosure ℚ)
          (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) n)
          g.toRingEquiv))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (N : ℕ)
    (g : Field.absoluteGaloisGroup ℚ) :
    ∃ (q : ℕ) (hq : q.Prime), N ≤ q ∧
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S ∧
      ∃ σ : Field.absoluteGaloisGroup ℚ,
        f g = f (σ * Field.absoluteGaloisGroup.map
          (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
          (Field.AbsoluteGaloisGroup.adicArithFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) * σ⁻¹) := by
  classical
  obtain ⟨n, hn, φ, hφ⟩ := hfactor
  let : NeZero n := ⟨hn.ne'⟩
  let χ := modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) n)
  let bound := S.sup fun v ↦ Nat.card
    (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))
  obtain ⟨q, hlarge, hq, hclass⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (χ g.toRingEquiv).isUnit (max N (max n bound))
  have hnq : n < q := lt_of_le_of_lt (le_trans (le_max_left n bound) (le_max_right _ _))
    hlarge
  have hcop : Nat.Coprime q n := hq.coprime_iff_not_dvd.mpr
    (fun h ↦ (Nat.le_of_dvd hn h).not_gt hnq)
  refine ⟨q, hq, le_of_lt (lt_of_le_of_lt (le_max_left _ _) hlarge), ?_, 1, ?_⟩
  · intro hmem
    have hle := Finset.le_sup (f := fun v : HeightOneSpectrum (𝓞 ℚ) ↦ Nat.card
      (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))) hmem
    rw [adicCompletion_residueField_card q hq] at hle
    have : bound < q := lt_of_le_of_lt
      (le_trans (le_max_right n bound) (le_max_right _ _)) hlarge
    exact this.not_ge hle
  · simp only [one_mul, inv_one, mul_one]
    rw [hφ, hφ]
    congr 1
    apply Units.ext
    exact hclass.symm.trans (modularCyclotomicCharacter_adicArithFrob n q hq hcop).symm

set_option backward.isDefEq.respectTransparency false in
/-- Frobenius traces `1 + q` and cyclotomic determinant imply reducibility.
Weak Chebotarev propagates the fixed-vector property through conjugate powers;
`not_isIrreducible_of_trace_eq_one_add_det` supplies the elementary rank-two
argument. No flatness or hardly-ramified hypothesis is used. -/
@[nolint unusedArguments]
theorem not_isIrreducible_of_frobenius_traces
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {k : Type} [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    [Algebra ℤ_[p] k] [IsLocalHom (algebraMap ℤ_[p] k)]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hdet : ∀ g, ρ.det g = algebraMap ℤ_[p] k
      (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (htrace : ∀ q (hq : Nat.Prime q), 5 ≤ q → q ≠ p →
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).trace k V = 1 + q) :
    ¬ ρ.IsIrreducible := by
  classical
  let : TopologicalSpace (Module.End k V) := moduleTopology k (Module.End k V)
  let : Finite (Module.End k V) := Module.finite_of_finite k
  let : T2Space (Module.End k V) := IsModuleTopology.t2Space k
  have hdim : Module.finrank k V = 2 := Module.finrank_eq_of_rank_eq hV
  apply not_isIrreducible_of_trace_eq_one_add_det hdim ρ.toRepresentation
  apply trace_identity_of_powerFrobCover hdim ρ S (p + 1)
    (powerFrobCover_of_finite ρ S (p + 1))
  intro q hq hlarge hqS
  have hq5 : 5 ≤ q := le_trans hp (by omega)
  have hqp : q ≠ p := by omega
  have hFdet : (ρ (QFrob q hq)).det = (q : k) := by
    change ρ.det (QFrob q hq) = _
    rw [hdet, cyclotomicCharacter_adicArithFrob p q hq hqp, map_natCast]
  rw [hFdet]
  exact htrace q hq hq5 hqp hqS

end FrobeniusTraces

end GaloisRepresentation.B5Inputs
