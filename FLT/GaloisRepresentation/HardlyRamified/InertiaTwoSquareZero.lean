/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.IntegralCharacters
public import FLT.FreyCurve.Serre.RootsOfUnityInertia
public import FLT.DedekindDomain.AdicValuation
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Square-zero inertia at two

Transport between the completion and the two-adic field preserves inertia.
The chosen global embeddings differ by a Galois automorphism, so the HR
quotient transports after conjugation. The cyclotomic determinant is one on
inertia at two, and the rank-two calculation gives square-zero unipotence.
This completes the integral-character theorem for reducible HR lattices.
-/

@[expose] public section

open Module
open scoped NumberField

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

/-- In rank two, a trivial free rank-one quotient and determinant one force
square-zero difference from the identity. -/
theorem sub_one_sq_eq_zero_of_trivial_quotient
    {O M : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (hdim : Module.finrank O M = 2) (f : Module.End O M)
    (π : M →ₗ[O] O) (hπ : Function.Surjective π)
    (hq : ∀ x, π (f x) = π x) (hdet : LinearMap.det f = 1) :
    (f - 1) ^ 2 = 0 := by
  let e := π.quotKerEquivOfSurjective hπ
  let : Module.Free O (M ⧸ LinearMap.ker π) := Module.Free.of_equiv e.symm
  have hqdim : Module.finrank O (M ⧸ LinearMap.ker π) = 1 := by
    rw [e.finrank_eq, Module.finrank_self]
  have hkdim : Module.finrank O (LinearMap.ker π) = 1 := by
    have h := (LinearMap.ker π).finrank_quotient_add_finrank
    rw [hqdim, hdim] at h
    omega
  have hstable : LinearMap.ker π ≤ (LinearMap.ker π).comap f := by
    intro x hx
    change π (f x) = 0
    rw [hq, hx]
  have hquot : (LinearMap.ker π).mapQ (LinearMap.ker π) f hstable = LinearMap.id := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (Submodule.Quotient.mk (f x) : M ⧸ LinearMap.ker π) =
        Submodule.Quotient.mk x
      rw [Submodule.Quotient.eq]
      simp [LinearMap.mem_ker, hq]
  obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hkdim
    (f.restrict hstable)
  have ha1 : a = 1 := by
    rw [f.det_eq_det_mul_det (LinearMap.ker π) hstable, ha, hquot,
      LinearMap.det_smul, hkdim, pow_one, LinearMap.det_id,
      LinearMap.det_id, mul_one, mul_one] at hdet
    exact hdet
  have hfix (x : LinearMap.ker π) : f x = (x : M) := by
    have h := congrArg (fun u : Module.End O (LinearMap.ker π) ↦ (u x : M)) ha
    simpa [ha1] using h
  ext x
  change f (f x - x) - (f x - x) = 0
  apply sub_eq_zero.mpr
  exact hfix ⟨f x - x, by simp [LinearMap.mem_ker, hq]⟩

/-- The residue field of the completion at a rational prime has that prime
as its cardinality. -/
theorem rationalCompletion_residueField_card (q : ℕ) (hq : q.Prime) :
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
  rw [← Nat.card_congr
    (IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField ℚ v).toEquiv,
    Nat.card_congr e.toEquiv, Nat.card_zmod]

/-- Local inertia fixes roots of unity of order prime to the residue
characteristic, using the integral-closure definition of local inertia. -/
theorem localInertia_fixes_of_pow_eq_one
    (n q : ℕ) (hn : 0 < n) (hq : q.Prime) (hcop : Nat.Coprime q n)
    (g : Field.absoluteGaloisGroup (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
    (hg : g ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
    (ζ : AlgebraicClosure (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
    (hζ : ζ ^ n = 1) : g ζ = ζ := by
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let R := v.adicCompletionIntegers ℚ
  let S := IntegralClosure R (AlgebraicClosure (v.adicCompletion ℚ))
  let Q := IsLocalRing.maximalIdeal S
  have hQR : Q.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.maximalIdeal_comap (algebraMap R S)
  have hnunit : IsUnit (n : S) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    have hqS : (q : S) ∈ Q := by
      have hqR : (q : R) ∈ IsLocalRing.maximalIdeal R := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        rw [map_natCast, ← rationalCompletion_residueField_card q hq]
        let := Fintype.ofFinite (IsLocalRing.ResidueField R)
        simpa only [Nat.card_eq_fintype_card] using
          Nat.cast_card_eq_zero (IsLocalRing.ResidueField R)
      rw [← map_natCast (algebraMap R S)]
      exact (show (q : R) ∈ Q.under R from hQR ▸ hqR)
    exact Ideal.IsPrime.notMem_of_isCoprime_of_mem
      (by simpa only [map_natCast] using hcop.isCoprime.map (Int.castRingHom S)) hqS
  let z : S := ⟨ζ, IsIntegral.of_pow hn (hζ ▸ isIntegral_one)⟩
  have hz : z ^ n = 1 := Subtype.ext hζ
  have hres : IsLocalRing.residue S (g • z) = IsLocalRing.residue S z := by
    apply sub_eq_zero.mp
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact (AddSubgroup.mem_inertia.mp hg) z
  have heq : g • z = z := IsLocalRing.eq_of_pow_eq_one_of_residue_eq hnunit
    (by rw [← smul_pow', hz, smul_one]) hz hres
  exact congrArg (algebraMap S (AlgebraicClosure (v.adicCompletion ℚ))) heq

/-- The p-adic cyclotomic character is trivial on local inertia at every
rational prime other than p, with the chosen global embedding. -/
@[nolint unusedArguments]
theorem cyclotomicCharacter_localInertia
    (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p)
    (g : Field.absoluteGaloisGroup (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
    (hg : g ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) :
    (cyclotomicCharacter (AlgebraicClosure ℚ) p
      (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
        g).toRingEquiv : ℤ_[p]) = 1 := by
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let f := algebraMap ℚ (v.adicCompletion ℚ)
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [cyclotomicCharacter.toZModPow, map_one]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : AlgebraicClosure ℚ) ^ (p ^ n) = 1 :=
    congrArg Units.val ((mem_rootsOfUnity (p ^ n) t).mp ht)
  have hlocal := localInertia_fixes_of_pow_eq_one (p ^ n) q
    (pow_pos (Fact.out : p.Prime).pos n) hq
    ((hq.coprime_iff_not_dvd.mpr (fun h ↦
      hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h))).pow_right n)
    g hg (AlgebraicClosure.map f t) (by rw [← map_pow, ht', map_one])
  have hglobal : Field.absoluteGaloisGroup.map f g t = (t : AlgebraicClosure ℚ) := by
    apply (AlgebraicClosure.map f).injective
    rw [Field.absoluteGaloisGroup.lift_map]
    exact hlocal
  change Field.absoluteGaloisGroup.map f g t = _
  rw [hglobal]
  simpa only [ZMod.val_one_eq_one_mod, pow_one] using (pow_eq_pow_mod 1 ht')

/-- The prime associated to the rational place at q is q. -/
theorem primesEquiv_ratPrime (q : ℕ) (hq : q.Prime) :
    Rat.HeightOneSpectrum.primesEquiv hq.toHeightOneSpectrumRingOfIntegersRat =
      ⟨q, hq⟩ := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective
  simp only [Equiv.symm_apply_apply]
  apply IsDedekindDomain.HeightOneSpectrum.ext
  change Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(q : ℤ)}) = _
  change _ = Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom
    (Ideal.span {(q : ℤ)})
  have he : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) = Rat.ringOfIntegersEquiv := by
    ext x
    exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  rw [he]
  exact (Ideal.map_symm (I := Ideal.span {(q : ℤ)}) Rat.ringOfIntegersEquiv).symm

/-- The rational place above two. -/
abbrev twoAdicPlace := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (by decide : Nat.Prime 2)

/-- The two-adic completion equivalence respects the integer subrings. -/
theorem exists_completionTwoEquiv :
    ∃ e : twoAdicPlace.adicCompletion ℚ ≃+* ℚ_[2],
      ∃ eR : twoAdicPlace.adicCompletionIntegers ℚ ≃+* ℤ_[2],
        ∀ x : twoAdicPlace.adicCompletionIntegers ℚ, (eR x : ℚ_[2]) = e x := by
  let : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv twoAdicPlace : ℕ)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv twoAdicPlace).property⟩
  have h : ∃ e : twoAdicPlace.adicCompletion ℚ ≃+*
      ℚ_[↑(Rat.HeightOneSpectrum.primesEquiv twoAdicPlace)],
      ∃ eR : twoAdicPlace.adicCompletionIntegers ℚ ≃+*
        ℤ_[↑(Rat.HeightOneSpectrum.primesEquiv twoAdicPlace)],
        ∀ x : twoAdicPlace.adicCompletionIntegers ℚ,
          (eR x : ℚ_[↑(Rat.HeightOneSpectrum.primesEquiv twoAdicPlace)]) = e x :=
    ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv twoAdicPlace).toRingEquiv,
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv twoAdicPlace).toRingEquiv,
      fun _ ↦ rfl⟩
  have hp : (Rat.HeightOneSpectrum.primesEquiv twoAdicPlace : ℕ) = 2 :=
    congrArg Subtype.val (primesEquiv_ratPrime 2 (by decide))
  have transport (p : ℕ) [Fact p.Prime] (hp : p = 2)
      (h : ∃ e : twoAdicPlace.adicCompletion ℚ ≃+* ℚ_[p],
        ∃ eR : twoAdicPlace.adicCompletionIntegers ℚ ≃+* ℤ_[p],
          ∀ x : twoAdicPlace.adicCompletionIntegers ℚ, (eR x : ℚ_[p]) = e x) :
      ∃ e : twoAdicPlace.adicCompletion ℚ ≃+* ℚ_[2],
        ∃ eR : twoAdicPlace.adicCompletionIntegers ℚ ≃+* ℤ_[2],
          ∀ x : twoAdicPlace.adicCompletionIntegers ℚ, (eR x : ℚ_[2]) = e x := by
    subst p
    exact h
  exact transport _ hp h

open Polynomial GaloisRepresentation

/-- Include two-adic integers into the valuation ring of the algebraic closure. -/
def padicIntegerToZ2bar : ℤ_[2] →+* Z2bar where
  toFun x := ⟨algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x, by
    change ‖algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x‖₊ ≤ 1
    rw [← NNReal.coe_le_coe]
    simpa using x.property⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

/-- The two-adic closure valuation ring is the integral closure of the two-adic integers. -/
theorem padicClosure_integral_iff (x : AlgebraicClosure ℚ_[2]) :
    IsIntegral ℤ_[2] x ↔ x ∈ Z2bar := by
  constructor
  · intro hx
    have hint : IsIntegral Z2bar x := by
      exact hx.map_of_comp_eq padicIntegerToZ2bar (RingHom.id _) (by ext; rfl)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    exact hy ▸ y.property
  · intro hx
    have hxnorm : spectralNorm ℚ_[2] (AlgebraicClosure ℚ_[2]) x ≤ 1 := by
      exact_mod_cast hx
    have hlifts : minpoly ℚ_[2] x ∈ Polynomial.lifts (algebraMap ℤ_[2] ℚ_[2]) := by
      refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
      have hcoeff : ‖(minpoly ℚ_[2] x).coeff i‖ ≤ 1 := by
        have h := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hxnorm i
        simp only [spectralValueTerms] at h
        split_ifs at h with hi
        · conv_rhs at h => rw [← Real.one_rpow (1 / (↑(minpoly ℚ_[2] x).natDegree - ↑i) : ℝ)]
          rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at h
          exact h
        obtain hi | hi := (le_of_not_gt hi).eq_or_lt
        · simp [← hi, minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral]
        · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]
      exact ⟨⟨_, hcoeff⟩, rfl⟩
    obtain ⟨P, hP, _, hmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts
      (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
    refine ⟨P, hmonic, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[2], hP, minpoly.aeval]


/-- Extend the completion equivalence to algebraic closures and their valuation rings. -/
theorem exists_closureTwoEquiv :
    ∃ e : twoAdicPlace.adicCompletion ℚ ≃+* ℚ_[2],
      ∃ E : AlgebraicClosure (twoAdicPlace.adicCompletion ℚ) ≃+* AlgebraicClosure ℚ_[2],
        (∀ x, E (algebraMap (twoAdicPlace.adicCompletion ℚ) _ x) =
          algebraMap ℚ_[2] _ (e x)) ∧
        ∃ eI : IntegralClosure (twoAdicPlace.adicCompletionIntegers ℚ)
          (AlgebraicClosure (twoAdicPlace.adicCompletion ℚ)) ≃+* Z2bar,
          ∀ x, (eI x : AlgebraicClosure ℚ_[2]) = E x.1 := by
  obtain ⟨e, eR, hR⟩ := exists_completionTwoEquiv
  let R := twoAdicPlace.adicCompletionIntegers ℚ
  let L := AlgebraicClosure (twoAdicPlace.adicCompletion ℚ)
  let E : L ≃+* AlgebraicClosure ℚ_[2] := IsAlgClosure.equivOfEquiv _ _ e
  have hcomp : (algebraMap ℤ_[2] (AlgebraicClosure ℚ_[2])).comp eR.toRingHom =
      E.toRingHom.comp (algebraMap R L) := by
    ext x
    change algebraMap ℚ_[2] _ (eR x : ℚ_[2]) =
      E (algebraMap (twoAdicPlace.adicCompletion ℚ) L x)
    rw [IsAlgClosure.equivOfEquiv_algebraMap, hR]
  have hcomp' : (algebraMap R L).comp eR.symm.toRingHom =
      E.symm.toRingHom.comp (algebraMap ℤ_[2] (AlgebraicClosure ℚ_[2])) := by
    ext x
    apply E.injective
    have h := RingHom.congr_fun hcomp (eR.symm x)
    change algebraMap ℤ_[2] _ (eR (eR.symm x)) = E (algebraMap R L (eR.symm x)) at h
    change E (algebraMap R L (eR.symm x)) = E (E.symm (algebraMap ℤ_[2] _ x))
    rw [E.apply_symm_apply, ← h, eR.apply_symm_apply]
  have hforward (x : IntegralClosure R L) : E x.1 ∈ Z2bar :=
    (padicClosure_integral_iff _).mp (x.property.map_of_comp_eq eR.toRingHom E.toRingHom hcomp)
  have hback (x : Z2bar) : IsIntegral R (E.symm x) :=
    ((padicClosure_integral_iff _).mpr x.property).map_of_comp_eq
      eR.symm.toRingHom E.symm.toRingHom hcomp'
  let eI : IntegralClosure R L ≃+* Z2bar :=
    { toFun := fun x ↦ ⟨E x.1, hforward x⟩
      invFun := fun x ↦ ⟨E.symm x, hback x⟩
      left_inv := fun x ↦ Subtype.ext (E.symm_apply_apply x.1)
      right_inv := fun x ↦ Subtype.ext (E.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (E.map_mul x.1 y.1)
      map_add' := fun x y ↦ Subtype.ext (E.map_add x.1 y.1) }
  exact ⟨e, E, IsAlgClosure.equivOfEquiv_algebraMap _ _ e, eI, fun _ ↦ rfl⟩

/-- An equivariant local-ring equivalence transports inertia. -/
theorem inertia_transport_of_ringEquiv
    {R S G H : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Group G] [Group H] [MulAction G R] [MulAction H S]
    (e : R ≃+* S) (g : G) (h : H) (he : ∀ x, e (g • x) = h • e x)
    (hg : g ∈ (IsLocalRing.maximalIdeal R).toAddSubgroup.inertia G) :
    h ∈ (IsLocalRing.maximalIdeal S).toAddSubgroup.inertia H := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← he, ← map_sub]
  have hx := hg x
  have hc := IsLocalRing.maximalIdeal_comap e.toRingHom
  change g • x - x ∈ IsLocalRing.maximalIdeal R at hx
  rw [← hc] at hx
  exact hx

/-- Compare two embeddings of an algebraic closure of the rationals. -/
theorem exists_global_embedding_comparison
    {L : Type*} [Field L] [CharZero L]
    (f₁ f₂ : AlgebraicClosure ℚ →+* L) :
    ∃ a : Field.absoluteGaloisGroup ℚ, ∀ x, f₂ (a x) = f₁ x := by
  let : Algebra (AlgebraicClosure ℚ) L := f₂.toAlgebra
  let : IsScalarTower ℚ (AlgebraicClosure ℚ) L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by simp
  let f : AlgebraicClosure ℚ →ₐ[ℚ] L :=
    { __ := f₁
      commutes' := fun x ↦ by simp }
  exact ⟨f.restrictNormal' (AlgebraicClosure ℚ), f.restrictNormal_commutes _⟩


/-- Transport local inertia at two to the two-adic Galois group, with the
conjugation accounting for the two chosen embeddings of the global closure. -/
theorem localInertiaTwo_transport
    (g : Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ))
    (hg : g ∈ localInertiaGroup twoAdicPlace) :
    ∃ h : Field.absoluteGaloisGroup ℚ_[2],
      h ∈ (IsLocalRing.maximalIdeal Z2bar).toAddSubgroup.inertia
        (Field.absoluteGaloisGroup ℚ_[2]) ∧
      ∃ a : Field.absoluteGaloisGroup ℚ,
        a * Field.absoluteGaloisGroup.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g =
          Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) h * a := by
  obtain ⟨e, E, he, eI, hI⟩ := exists_closureTwoEquiv
  have he' (x : ℚ_[2]) : E.symm (algebraMap ℚ_[2] _ x) =
      algebraMap (twoAdicPlace.adicCompletion ℚ) _ (e.symm x) := by
    apply E.injective
    rw [E.apply_symm_apply, he, e.apply_symm_apply]
  let h : Field.absoluteGaloisGroup ℚ_[2] :=
    { __ := E.symm.trans (g.toRingEquiv.trans E)
      commutes' := fun x ↦ by
        change E (g (E.symm (algebraMap ℚ_[2] _ x))) = algebraMap ℚ_[2] _ x
        rw [he', g.commutes, he, e.apply_symm_apply] }
  have hact (x : IntegralClosure (twoAdicPlace.adicCompletionIntegers ℚ)
      (AlgebraicClosure (twoAdicPlace.adicCompletion ℚ))) : eI (g • x) = h • eI x := by
    apply Subtype.ext
    rw [hI]
    change E (g x.1) = E (g (E.symm (eI x)))
    rw [hI, E.symm_apply_apply]
  have hh := inertia_transport_of_ringEquiv eI g h hact hg
  let f := algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)
  let f₂ := algebraMap ℚ ℚ_[2]
  obtain ⟨a, ha⟩ := exists_global_embedding_comparison
    (E.toRingHom.comp (AlgebraicClosure.map f)) (AlgebraicClosure.map f₂)
  refine ⟨h, hh, a, ?_⟩
  apply AlgEquiv.ext
  intro x
  apply (AlgebraicClosure.map f₂).injective
  change AlgebraicClosure.map f₂ (a (Field.absoluteGaloisGroup.map f g x)) =
    AlgebraicClosure.map f₂ (Field.absoluteGaloisGroup.map f₂ h (a x))
  rw [ha, Field.absoluteGaloisGroup.lift_map]
  change E (AlgebraicClosure.map f (Field.absoluteGaloisGroup.map f g x)) =
    h (AlgebraicClosure.map f₂ (a x))
  rw [Field.absoluteGaloisGroup.lift_map, ha]
  change E (g (AlgebraicClosure.map f x)) =
    E (g (E.symm (E (AlgebraicClosure.map f x))))
  rw [E.symm_apply_apply]

/-- The HR determinant is one on inertia at two. -/
theorem hardlyRamified_det_on_inertiaTwo
    {O M : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [IsLocalRing O] [Algebra ℤ_[3] O] [AddCommGroup M] [Module O M]
    [Module.Free O M] [Module.Finite O M]
    (hdim : Module.rank O M = 2) (ρ : GaloisRep ℚ O M)
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hdim ρ)
    (g : Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ))
    (hg : g ∈ localInertiaGroup twoAdicPlace) :
    LinearMap.det (ρ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g)) = 1 := by
  rw [show LinearMap.det (ρ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g)) = _ from hρ.det _]
  rw [cyclotomicCharacter_localInertia 3 2 (by decide) (by decide) g hg, map_one]

/-- The unramified quotient at two and the cyclotomic determinant in HR
force square-zero inertia for the number-field completion definition. -/
theorem hardlyRamified_inertiaTwo_sq_zero
    {O M : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [IsLocalRing O] [Algebra ℤ_[3] O]
    [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (hdim : Module.rank O M = 2) (ρ : GaloisRep ℚ O M)
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hdim ρ)
    (g : Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ))
    (hg : g ∈ localInertiaGroup twoAdicPlace) :
    (ρ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g) - 1) ^ 2 = 0 := by
  obtain ⟨h, hh, a, ha⟩ := localInertiaTwo_transport g hg
  obtain ⟨π, hπ, δ, hδ⟩ := hρ.isTameAtTwo
  have hhδ : δ h = 1 := (hδ 1 0).2.1 hh
  let π' : M →ₗ[O] O := π.comp (ρ a)
  have hs : Function.Surjective (ρ a) := by
    intro x
    refine ⟨ρ a⁻¹ x, ?_⟩
    change (ρ a * ρ a⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  apply sub_one_sq_eq_zero_of_trivial_quotient (Module.finrank_eq_of_rank_eq hdim)
    _ π' (hπ.comp hs) _ (hardlyRamified_det_on_inertiaTwo hdim ρ hρ g hg)
  intro x
  have he : ρ a (ρ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g) x) =
      ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) h) (ρ a x) := by
    have he := congrArg (fun k : Field.absoluteGaloisGroup ℚ ↦ ρ k x) ha
    simpa only [map_mul, Module.End.mul_apply] using he
  change π (ρ a (ρ _ x)) = π (ρ a x)
  rw [he]
  have hquot := (hδ h (ρ a x)).1
  rw [hhδ] at hquot
  convert hquot using 1
  congr 3

section HardlyRamified

variable {O K W : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
  [TopologicalSpace O] [IsTopologicalRing O]
  [TopologicalSpace K] [IsTopologicalRing K] [Algebra ℤ_[3] O]

/-- Reducibility of a hardly-ramified three-adic lattice gives integral
characters unramified outside three, finite flat at three, and with
cyclotomic product. -/
theorem integral_characters_of_reducible (ρK : GaloisRep ℚ K W)
    (Λ : Submodule O W) (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (hdim : Module.rank K W = 2)
    (hρΛ : letI := hΛ.isLattice
      GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide)
        ((Submodule.IsLattice.rank' K Λ).trans hdim) (latticeGaloisRep ρK Λ hΛ hOK))
    (hred : ¬ ρK.IsIrreducible) :
    ∃ ψ₁ ψ₂ : Field.absoluteGaloisGroup ℚ →* Oˣ,
      Continuous ψ₁ ∧ Continuous ψ₂ ∧ Flat3 ψ₁ ∧ Flat3 ψ₂ ∧
      UnramifiedOutsideThree ψ₁ ∧ UnramifiedOutsideThree ψ₂ ∧
      GenericExtensionOf ρK.toRepresentation ψ₁ ψ₂ ∧ ψ₁ * ψ₂ = threeAdicCyclotomic := by
  apply integral_characters_of_reducible_of_inertia_two ρK Λ hΛ hOK hdim hρΛ hred
  let := hΛ.isLattice
  dsimp only
  intro g hg
  convert hardlyRamified_inertiaTwo_sq_zero
    ((Submodule.IsLattice.rank' K Λ).trans hdim)
    (latticeGaloisRep ρK Λ hΛ hOK) hρΛ g hg using 1
  congr 5
  exact Subsingleton.elim _ _

end HardlyRamified

end ThreeAdicPlan
