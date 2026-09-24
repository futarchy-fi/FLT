/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.Unramified
public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Instances.ZMod

import Mathlib.NumberTheory.NumberField.ExistsRamified

/-!
# Everywhere-unramified characters over the rationals

A continuous character over a finite field cuts out a finite Galois extension.
Trivial local inertia forces ramification index one in each corresponding completion,
hence at each induced global prime. Minkowski's theorem then forces the extension
to be the rational field and the character to be trivial.
-/

@[expose] public section

open NumberField IntermediateField NumberField.InertiaComparison

namespace NumberField.InertiaComparison

/-- The ring of rational integers is formally unramified over the integers. -/
lemma rationalIntegers_formallyUnramified : Algebra.FormallyUnramified ℤ (𝓞 ℚ) := by
  apply Algebra.FormallyUnramified.of_surjective
    (Algebra.ofId ℤ (𝓞 ℚ))
  have heq : (algebraMap ℤ (𝓞 ℚ)) = Rat.ringOfIntegersEquiv.symm.toRingHom :=
    Subsingleton.elim _ _
  change Function.Surjective (algebraMap ℤ (𝓞 ℚ))
  rw [heq]
  exact Rat.ringOfIntegersEquiv.symm.surjective

/-- The rational prime belongs to the prime induced in a finite global extension. -/
lemma prime_mem_localInducedPrime
    (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (q : ℕ) (hq : q.Prime) :
    (q : 𝓞 L) ∈ localInducedPrime hq.toHeightOneSpectrumRingOfIntegersRat L := by
  have hqv : (q : 𝓞 ℚ) ∈ hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
    change Rat.ringOfIntegersEquiv (q : 𝓞 ℚ) ∈ Ideal.span {(q : ℤ)}
    rw [map_natCast]
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa only [map_natCast] using
    (Ideal.mem_of_liesOver (localInducedPrime hq.toHeightOneSpectrumRingOfIntegersRat L)
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal (q : 𝓞 ℚ)).mp hqv

/-- A finite Galois subextension of `ℚbar` with trivial local inertia is `ℚ`. -/
lemma intermediateField_eq_bot_of_localInertia
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [Normal ℚ L]
    (h : ∀ (q : ℕ) (hq : q.Prime), localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
      (localRestriction hq.toHeightOneSpectrumRingOfIntegersRat L).ker) : L = ⊥ := by
  let : IsGalois ℚ L := {}
  apply IntermediateField.finrank_eq_one_iff.mp
  by_contra hn
  have hgt : 1 < Module.finrank ℚ L := lt_of_le_of_ne (Module.finrank_pos) (Ne.symm hn)
  obtain ⟨q, hq, hram⟩ := NumberField.exists_not_isUnramifiedAt_int_of_isGalois
    (K := L) (𝒪 := 𝓞 L) hgt
  let P := localInducedPrime hq.toHeightOneSpectrumRingOfIntegersRat L
  let : Algebra.IsUnramifiedAt (𝓞 ℚ) P :=
    localInducedPrime_isUnramifiedAt _ L (h q hq)
  let : Algebra.FormallyUnramified ℤ (𝓞 ℚ) := rationalIntegers_formallyUnramified
  have hp : Algebra.IsUnramifiedAt ℤ P :=
    Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime P)
  exact hram P inferInstance (prime_mem_localInducedPrime L q hq) hp

end NumberField.InertiaComparison

namespace GaloisRep

/-- The kernel of a character over a finite field is open. -/
lemma character_ker_isOpen {p : ℕ} [Fact p.Prime]
    (χ : GaloisRep ℚ (ZMod p) (ZMod p)) : IsOpen (χ.ker : Set (Field.absoluteGaloisGroup ℚ)) := by
  let := moduleTopology (ZMod p) (Module.End (ZMod p) (ZMod p))
  let : DiscreteTopology (Module.End (ZMod p) (ZMod p)) := by
    constructor
    change moduleTopology (ZMod p) (Module.End (ZMod p) (ZMod p)) = ⊥
    let : TopologicalSpace (Module.End (ZMod p) (ZMod p)) := ⊥
    let : DiscreteTopology (Module.End (ZMod p) (ZMod p)) := ⟨rfl⟩
    let : ContinuousSMul (ZMod p) (Module.End (ZMod p) (ZMod p)) :=
      ⟨continuous_of_discreteTopology⟩
    let : ContinuousAdd (Module.End (ZMod p) (ZMod p)) :=
      ⟨continuous_of_discreteTopology⟩
    exact le_bot_iff.mp (moduleTopology_le (ZMod p) (Module.End (ZMod p) (ZMod p)))
  change IsOpen (χ ⁻¹' {1})
  exact (isOpen_discrete {1}).preimage χ.continuous

/-- Every everywhere-unramified finite-field character of the rational absolute Galois group
is trivial. -/
theorem trivial_of_everywhere_unramified {p : ℕ} [Fact p.Prime]
    (χ : GaloisRep ℚ (ZMod p) (ZMod p))
    (hχ : ∀ (q : ℕ) (hq : q.Prime), χ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∀ g x, χ g x = x := by
  let H : OpenNormalSubgroup (Field.absoluteGaloisGroup ℚ) := {
    toSubgroup := χ.ker
    isOpen' := character_ker_isOpen χ
    isNormal' := inferInstance }
  let C : ClosedSubgroup (Field.absoluteGaloisGroup ℚ) :=
    ⟨H.toSubgroup, H.toOpenSubgroup.isClosed⟩
  let L := IntermediateField.fixedField H.toSubgroup
  let : IsGalois ℚ L := IsGalois.of_fixedField_normal_subgroup H.toSubgroup
  have hfix : L.fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField C
  let : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (hfix.symm ▸ H.isOpen')
  have hbot : L = ⊥ := by
    apply intermediateField_eq_bot_of_localInertia L
    intro q hq σ hσ
    have hker := (hχ q hq).localInertiaGroup_le hσ
    let f : ℚ →+* hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ :=
      @algebraMap ℚ _ _ _ (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (𝓞 ℚ) ℚ hq.toHeightOneSpectrumRingOfIntegersRat)
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact (AlgEquiv.restrictNormalHom_apply L
      (Field.absoluteGaloisGroup.map f σ) x).trans
        (x.2 ⟨Field.absoluteGaloisGroup.map f σ, hker⟩)
  have htop : χ.ker = ⊤ := by
    change H.toSubgroup = ⊤
    rw [← hfix, hbot, IntermediateField.fixingSubgroup_bot]
  intro g x
  have hg : χ g = 1 := by
    change g ∈ χ.ker
    rw [htop]
    trivial
  rw [hg]
  rfl

end GaloisRep
