/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.SupersingularPolynomial
public import FLT.EllipticCurve.TorsionOrbit
public import FLT.FreyCurve.Serre.GoodReductionAtP
public import FLT.FreyCurve.Serre.GoodReductionSpecialization
public import FLT.FreyCurve.Serre.LocalUniformizer

/-!
# An inertia-invariant quotient at the torsion prime

A stable line rules out trivial geometric special-fiber torsion by the Eisenstein
criterion for the reversed division polynomial. Surjective, inertia-invariant
specialization then supplies a nonzero invariant functional. This proves
`GoodReductionAtPQuotient` for primes at least five, using the pre-existing
`n_torsion_card` admission and no torsion-flatness admission.
-/

@[expose] public section

open NumberField IsLocalRing ValuativeRel Polynomial
attribute [local instance] completionValuativeRel completion_isNonarchimedeanLocalField
set_option quotPrecheck false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace WeierstrassCurve
variable (p : ℕ) (hp : p.Prime)
local notation "v" => hp.toHeightOneSpectrumRingOfIntegersRat
local notation "K" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "R" => 𝒪[K]
local notation "Ω" => AlgebraicClosure K
local notation "κ" => ResidueField R
local notation "κbar" => AlgebraicClosure κ
/-- Classical equality for local geometric coordinates. -/
noncomputable local instance goodReductionAtPProofDecidableEq (α : Type*) : DecidableEq α :=
  Classical.typeDecidableEq α

/-- Over `ℚ_p`, a Galois-stable prime-order line forces nontrivial geometric
special-fiber torsion. The supersingular alternative would give an Eisenstein
division polynomial and a transitive Galois orbit incompatible with a line. -/
theorem stableLine_forces_nontrivial_specialFiber (hp5 : 5 ≤ p)
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasGoodReduction R]
    (hline : letI : Fact p.Prime := ⟨hp⟩
      ∃ i : ZMod p →ₗ[ZMod p] (E.map (algebraMap K Ω)).nTorsion p,
        Function.Injective i ∧ ∀ σ : Field.absoluteGaloisGroup K,
          ∃ a : ZMod p, E.galoisRep p hp.pos σ (i 1) = i a) :
    Nontrivial (((E.reduction R).map (algebraMap κ κbar)).nTorsion p) := by
  let : Fact p.Prime := ⟨hp⟩
  by_contra hn
  have hsub := not_nontrivial_iff_subsingleton.mp hn
  let W := E.integralModel R
  have hgen : W.map (algebraMap R K) = E := E.baseChange_integralModel_eq R
  have hred : W.map (residue R) = E.reduction R := rfl
  have : (W.map (residue R)).IsElliptic :=
    hred.symm ▸ (hasGoodReduction_iff_isElliptic_reduction R (W := E)).mp inferInstance
  have hno : ∀ P : ((W.map (residue R)).map (algebraMap κ κbar)).toAffine.Point,
      p • P = 0 → P = 0 := by
    intro P hP
    let Q : ((E.reduction R).map (algebraMap κ κbar)).nTorsion p :=
      ⟨P, by
        change (p : ℤ) • P = 0
        simpa only [natCast_zsmul] using hP⟩
    exact congrArg Subtype.val (Subsingleton.elim Q 0)
  have ho : ¬ Even p := by
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two (by omega)
    rintro ⟨k, hk⟩
    omega
  let f := (W.preΨ' p).reverse.map (algebraMap R K)
  have hirr : Irreducible f := irreducible_reverse_preΨ'_of_torsion_trivial R K W p
    (by omega) ho (prime_notMem_square_maximalIdeal p hp) hno
  apply no_stableLine_of_irreducible_inverseX E p hp f hirr ?_ hline
  intro x y h ht
  have hψ : ((E.map (algebraMap K Ω)).preΨ' p).IsRoot x := by
    have hh := (E.map (algebraMap K Ω)).isRoot_ΨSq_of_nsmul_eq_zero h p ht
    rw [ΨSq_ofNat, ite_eq_right ho, mul_one] at hh
    exact eq_zero_of_pow_eq_zero (by simpa only [IsRoot, eval_pow] using hh)
  have hmap : (W.preΨ' p).map (algebraMap R K) = E.preΨ' p := by
    rw [← map_preΨ', hgen]
  have hv : aeval x ((W.preΨ' p).map (algebraMap R K)) = 0 := by
    rw [hmap]
    change eval₂ (algebraMap K Ω) x (E.preΨ' p) = 0
    rw [← eval_map, ← map_preΨ']
    exact hψ
  have heval : (W.preΨ' p).eval₂ (algebraMap R Ω) x = 0 := by
    simpa only [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq] using hv
  have hu : IsUnit ((W.preΨ' p).map (residue R)) := by
    have hh := isUnit_preΨ'_of_torsion_trivial
      ((W.map (residue R)).map (algebraMap κ κbar)) p hno
    rw [map_preΨ', map_preΨ', Polynomial.isUnit_iff_degree_eq_zero, degree_map] at hh
    exact Polynomial.isUnit_iff_degree_eq_zero.mpr hh
  have hc0 : (W.preΨ' p).coeff 0 ≠ 0 := by
    intro hz
    apply hu.ne_zero
    have hh := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hu)
    simpa only [coeff_map, hz, map_zero, C_0] using hh
  have hx0 : x ≠ 0 := by
    intro hx
    have hh : algebraMap R Ω ((W.preΨ' p).coeff 0) = 0 := by
      simpa only [hx, eval₂_at_zero] using heval
    apply hc0
    apply IsFractionRing.injective R K
    apply (algebraMap K Ω).injective
    simpa only [map_zero, ← IsScalarTower.algebraMap_apply] using hh
  let := invertibleOfNonzero hx0
  have hh := (eval₂_reverse_eq_zero_iff (algebraMap R Ω) x (W.preΨ' p)).mpr heval
  simpa only [f, aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq, invOf_eq_inv] using hh
end WeierstrassCurve

namespace WeierstrassCurve

/-- Good reduction and a Galois-stable line over `ℚ_p`, for `p ≥ 5`, give a
nonzero inertia-invariant functional on geometric prime torsion. The only
inherited geometric admission used by this proof is `n_torsion_card`. -/
theorem goodReductionAtPQuotient (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    GoodReductionAtPQuotient p hp := by
  let : Fact p.Prime := ⟨hp⟩
  intro E hE hgood hline
  let := hE
  let := hgood
  let := stableLine_forces_nontrivial_specialFiber p hp hp5 E hline
  exact E.exists_inertiaInvariant_functional_of_nontrivial_reduction
    hp.toHeightOneSpectrumRingOfIntegersRat p hp

end WeierstrassCurve
