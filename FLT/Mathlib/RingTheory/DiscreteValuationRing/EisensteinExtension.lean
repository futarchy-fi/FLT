/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.AdjoinRoot
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.Eisenstein
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Totally ramified extensions from Eisenstein perturbations

A root of a monic Eisenstein polynomial generates an extension of the expected
degree. Its ring of integers is the polynomial quotient, and the root is a
uniformizer. A monomial perturbation therefore realizes an exact polynomial
valuation in an extension of the same degree and ramification index.
-/

@[expose] public noncomputable section

universe u

open Polynomial IsLocalRing

namespace AdjoinRoot

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {P : R[X]}

/-- The field quotient of an Eisenstein polynomial is the fraction field of
its integral polynomial quotient. -/
theorem isFractionRingMapOfEisenstein
    (hP : P.IsEisensteinAt (maximalIdeal R)) (hPm : P.Monic) (hdeg : 0 < P.natDegree)
    [IsDomain (AdjoinRoot P)] [IsDiscreteValuationRing (AdjoinRoot P)]
    [Fact (Irreducible (P.map (algebraMap R K)))]
    [Algebra (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))]
    [IsScalarTower R (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))]
    (hmap : (algebraMap (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))).comp (mk P)
      = (mk (P.map (algebraMap R K))).comp (Polynomial.mapRingHom (algebraMap R K))) :
    IsFractionRing (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K))) := by
  let S := AdjoinRoot P
  let E := AdjoinRoot (P.map (algebraMap R K))
  have hinj : Function.Injective (algebraMap R S) :=
    of.injective_of_monic_of_degree_pos hPm (natDegree_pos_iff_degree_pos.mp hdeg)
  have hRE : Function.Injective (algebraMap R E) := by
    rw [IsScalarTower.algebraMap_eq R K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective R K)
  have hroot : algebraMap S E (root P) = root (P.map (algebraMap R K)) := by
    have h := RingHom.congr_fun hmap X
    simpa using h
  have hroot0 : root (P.map (algebraMap R K)) ≠ 0 := by
    intro hz
    have hv : aeval (root (P.map (algebraMap R K))) P = 0 := by
      rw [aeval_eq_of_algebra]
      exact mk_self
    have hc : algebraMap R E (P.coeff 0) = 0 := by
      rwa [hz, ← coeff_zero_eq_aeval_zero'] at hv
    exact (hP.irreducibleCoeffZero hdeg).ne_zero (hRE (by simpa using hc))
  have hmax : maximalIdeal S = Ideal.span {root P} :=
    maximalIdealEqSpanRootOfEisenstein hP hPm hdeg _ inferInstance
  have hSE : Function.Injective (algebraMap S E) :=
    IsDiscreteValuationRing.injective_of_not_maximalIdeal_le_ker _ fun hle => by
      have h := hle (hmax.symm ▸ Ideal.subset_span (Set.mem_singleton (root P)))
      exact hroot0 (hroot.symm.trans h)
  refine (_root_.isLocalization_iff (nonZeroDivisors S) E).mpr ⟨fun y => ?_, fun z => ?_,
    fun {x y} h => ⟨1, by rw [hSE h]⟩⟩
  · exact isUnit_iff_ne_zero.mpr fun h =>
      nonZeroDivisors.ne_zero y.2 (hSE (by rw [h, map_zero]))
  · obtain ⟨b, hb, x, hx⟩ := exists_nonZeroDivisor_mul_eq_algebraMap hmap z
    refine ⟨⟨x, ⟨algebraMap R S b, mem_nonZeroDivisors_of_ne_zero fun h =>
      nonZeroDivisors.ne_zero hb (hinj (by rw [h, map_zero]))⟩⟩, ?_⟩
    rwa [← IsScalarTower.algebraMap_apply R S E]

end AdjoinRoot

namespace Polynomial.IsEisensteinAt

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {P : R[X]}

/-- Every monic positive-degree Eisenstein polynomial constructs a finite
extension with integral power basis and the expected uniformizer valuation. -/
theorem existsTotallyRamifiedExtension (hP : P.IsEisensteinAt (maximalIdeal R))
    (hPm : P.Monic) (hdeg : 0 < P.natDegree) {π : R} (hπ : Irreducible π) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (_ : Algebra R E) (_ : IsScalarTower R K E) (S : Type u) (_ : CommRing S)
      (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S E) (_ : IsScalarTower R S E)
      (_ : IsFractionRing S E) (_ : IsIntegralClosure S R E) (y : S),
      Module.finrank K E = P.natDegree ∧ Irreducible y ∧ aeval y P = 0 ∧
        IsDiscreteValuationRing.addVal S (algebraMap R S π) = (P.natDegree : ℕ∞) ∧
        Algebra.adjoin R {y} = ⊤ := by
  have hPi : Irreducible P := hP.irreducible inferInstance hPm.isPrimitive hdeg
  let q := P.map (algebraMap R K)
  let instIrreducible : Fact (Irreducible q) :=
    ⟨hPm.irreducible_iff_irreducible_map_fraction_map.mp hPi⟩
  let E := AdjoinRoot q
  let S := AdjoinRoot P
  let instDomain : IsDomain S :=
    AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hPi)
  obtain ⟨instDvr, hy⟩ := AdjoinRoot.isDiscreteValuationRingOfEisenstein hP hPm hdeg
  let instFinite : Module.Finite R S := hPm.finite_adjoinRoot
  let algSE : Algebra S E := (AdjoinRoot.map (algebraMap R K) P q dvd_rfl).toAlgebra
  have halg : algebraMap S E = AdjoinRoot.map (algebraMap R K) P q dvd_rfl :=
    RingHom.algebraMap_toAlgebra _
  let instTower : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg, AdjoinRoot.algebraMap_eq (f := P), AdjoinRoot.map_of, AdjoinRoot.algebraMap_eq']
    rfl
  let instFraction : IsFractionRing S E :=
    AdjoinRoot.isFractionRingMapOfEisenstein hP hPm hdeg
      (by rw [halg]; exact AdjoinRoot.map_comp_mk (algebraMap R K) rfl)
  let instClosure : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  refine ⟨E, inferInstance, inferInstance, (AdjoinRoot.powerBasis (hPm.map _).ne_zero).finite,
    inferInstance, inferInstance, S, inferInstance, instDomain, instDvr, inferInstance,
    instFinite, algSE, instTower, instFraction, instClosure, AdjoinRoot.root P,
    ?_, hy, by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self], ?_,
    AdjoinRoot.adjoinRoot_eq_top⟩
  · rw [(AdjoinRoot.powerBasis (hPm.map (algebraMap R K)).ne_zero).finrank]
    exact hPm.natDegree_map _
  · rw [hP.addValUniformizerEqDegreeMul hPm hdeg hπ hy.not_isUnit
      (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]),
      IsDiscreteValuationRing.addVal_uniformizer hy, nsmul_one]

/-- A perturbation with exponent decomposition `n*r+s` constructs an integral
root whose original polynomial value has exactly that additive valuation. -/
theorem existsPerturbedExtensionWithValuation
    (hP : P.IsEisensteinAt (maximalIdeal R)) (hPm : P.Monic)
    {π : R} (hπ : Irreducible π) (r s : ℕ) (hr : 0 < r)
    (hs : s < P.natDegree) (hr0 : s = 0 → 2 ≤ r) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (_ : Algebra R E) (_ : IsScalarTower R K E) (S : Type u) (_ : CommRing S)
      (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S E) (_ : IsScalarTower R S E)
      (_ : IsFractionRing S E) (_ : IsIntegralClosure S R E) (y : S),
      Module.finrank K E = P.natDegree ∧ Irreducible y ∧
        IsDiscreteValuationRing.addVal S (algebraMap R S π) = (P.natDegree : ℕ∞) ∧
        IsDiscreteValuationRing.addVal S (aeval y P) = (P.natDegree * r + s : ℕ) := by
  have ha : π ^ r ∈ maximalIdeal R :=
    (maximalIdeal R).pow_mem_of_mem hπ.not_isUnit _ hr
  have ha0 : s = 0 → π ^ r ∈ maximalIdeal R ^ 2 := by
    intro hs0
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact pow_dvd_pow π (hr0 hs0)
  let Q := P - monomial s (π ^ r)
  have hQ : Q.IsEisensteinAt (maximalIdeal R) := hP.subMonomial hs ha ha0
  have hQm : Q.Monic := hPm.subMonomial hs
  have hQdeg : Q.natDegree = P.natDegree := natDegreeSubMonomial hs
  obtain ⟨E, instField, instAlgK, instFinite, instAlgR, instTowerK, S, instRing,
    instDomain, instDvr, instAlgS, instFiniteS, instAlgSE, instTowerS, instFraction,
    instClosure, y, hdeg, hy, hroot, hval, _⟩ :=
      hQ.existsTotallyRamifiedExtension (K := K) hQm
        (hQdeg ▸ (Nat.zero_le s).trans_lt hs) hπ
  refine ⟨E, instField, instAlgK, instFinite, instAlgR, instTowerK, S, instRing,
    instDomain, instDvr, instAlgS, instFiniteS, instAlgSE, instTowerS, instFraction,
    instClosure, y, hdeg.trans hQdeg, hy, hQdeg ▸ hval, ?_⟩
  rw [aevalEqOfSubMonomialRoot y hroot, map_pow,
    IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_pow, hval, hQdeg,
    IsDiscreteValuationRing.addVal_uniformizer hy, nsmul_one]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]
  rw [mul_comm]

end Polynomial.IsEisensteinAt
