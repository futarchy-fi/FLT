/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.Unramified
public import FLT.GaloisRepresentation.HardlyRamified.ResidualTameTwo
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Cyclic quotients of tame inertia

For a finite faithful action on a discrete valuation ring, the uniformizer
character embeds tame inertia in residue-field units. Its kernel is a
`p`-group: a prime-to-`p` torsion element acts trivially on every successive
ideal quotient, hence on the ring by Krull intersection.

Consequently every finite prime-to-`p` inertia quotient is cyclic. We pass
from absolute inertia to a finite Galois extension using the open kernel
of the action, and deduce `ramification_two_dvd_three` for finite discrete
representations killed by three with square-zero inertia at two.
-/

@[expose] public section

noncomputable section

namespace ThreeAdicPlan

/-- A homomorphism from a `p`-group to a finite group of order prime to `p`
is trivial. No finiteness assumption on the source is needed. -/
@[nolint unusedArguments]
theorem pGroup_hom_eq_one_of_coprime_card
    {p : ℕ} {P H : Type*} [Group P] [Group H] [Finite H]
    (hP : IsPGroup p P) (hH : Nat.Coprime p (Nat.card H)) (f : P →* H) :
    f = 1 := by
  apply MonoidHom.ext
  intro g
  obtain ⟨n, hn⟩ := hP g
  apply (pow_eq_one_iff_of_coprime (hH.pow_left n)).mp
  exact ⟨by rw [← map_pow, hn, map_one], pow_card_eq_one'⟩

/-- A prime-to-`p` finite quotient of a group with cyclic quotient by a
normal `p`-subgroup is cyclic. -/
theorem isCyclic_of_surjective_of_pGroup_kernel
    {p : ℕ} {G H : Type*} [Group G] [Group H] [Finite H]
    (P : Subgroup G) [P.Normal] [IsCyclic (G ⧸ P)]
    (hP : IsPGroup p P) (hH : Nat.Coprime p (Nat.card H))
    (f : G →* H) (hf : Function.Surjective f) : IsCyclic H := by
  have htriv := pGroup_hom_eq_one_of_coprime_card hP hH (f.comp P.subtype)
  have hker : P ≤ f.ker := by
    intro g hg
    exact DFunLike.congr_fun htriv ⟨g, hg⟩
  let f' := QuotientGroup.lift P f hker
  apply isCyclic_of_surjective f'
  intro h
  obtain ⟨g, rfl⟩ := hf h
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- A residue-field character with `p`-group kernel makes every finite
prime-to-`p` quotient cyclic. The finite source gives a finite character
image; the field itself need not be finite. -/
theorem isCyclic_of_residue_character
    {p : ℕ} {G H k : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Field k] (χ : G →* kˣ) (hχ : IsPGroup p χ.ker)
    (hH : Nat.Coprime p (Nat.card H)) (f : G →* H)
    (hf : Function.Surjective f) : IsCyclic H := by
  let : Finite χ.range := Finite.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  let : IsCyclic χ.range := isCyclic_subgroup_units χ.range
  let : IsCyclic (G ⧸ χ.ker) :=
    (QuotientGroup.quotientKerEquivRange χ).isCyclic.mpr inferInstance
  exact isCyclic_of_surjective_of_pGroup_kernel χ.ker hχ hH f hf

section DiscreteValuationRing

open IsLocalRing

variable {A G : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Group G] [MulSemiringAction G A]
  {π : A} (hπ : Irreducible π)

/-- The unit multiplying a uniformizer under a ring automorphism. -/
def uniformizerRatio (g : G) : Aˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible A hπ
    (hπ.map (MulSemiringAction.toRingAut G A g))).choose

/-- The chosen unit really is the ratio `g(π)/π`. -/
theorem uniformizer_mul_ratio (g : G) :
    π * (uniformizerRatio hπ g : A) = g • π :=
  (IsDiscreteValuationRing.associated_of_irreducible A hπ
    (hπ.map (MulSemiringAction.toRingAut G A g))).choose_spec

/-- Inertia acts trivially on every residue class. -/
theorem residue_inertia_smul (g : (maximalIdeal A).inertia G) (a : A) :
    residue A (g.val • a) = residue A a :=
  Ideal.Quotient.eq.mpr (Ideal.mem_inertia.mp g.property a)

/-- The tame character on inertia, obtained by reducing `g(π)/π`. -/
def uniformizerCharacter : (maximalIdeal A).inertia G →* (ResidueField A)ˣ where
  toFun g := Units.map (residue A).toMonoidHom (uniformizerRatio hπ g.val)
  map_one' := by
    apply Units.ext
    change residue A (uniformizerRatio hπ (1 : G) : A) = 1
    have h : (uniformizerRatio hπ (1 : G) : A) = 1 := by
      apply mul_left_cancel₀ hπ.ne_zero
      simpa using uniformizer_mul_ratio hπ (1 : G)
    rw [h, map_one]
  map_mul' g h := by
    apply Units.ext
    change residue A (uniformizerRatio hπ (g.val * h.val) : A) =
      residue A (uniformizerRatio hπ g.val : A) *
        residue A (uniformizerRatio hπ h.val : A)
    have hc : (uniformizerRatio hπ (g.val * h.val) : A) =
        (uniformizerRatio hπ g.val : A) * (g.val • (uniformizerRatio hπ h.val : A)) := by
      apply mul_left_cancel₀ hπ.ne_zero
      rw [uniformizer_mul_ratio, ← mul_assoc, uniformizer_mul_ratio,
        ← smul_mul', uniformizer_mul_ratio, mul_smul]
    rw [hc, map_mul, residue_inertia_smul]

/-- An element of the kernel acts trivially on every associated graded
piece of the maximal-ideal filtration. -/
theorem uniformizerCharacter_ker_smul_sub_mem
    (g : (maximalIdeal A).inertia G) (hg : uniformizerCharacter hπ g = 1)
    (n : ℕ) (a : A) (ha : a ∈ maximalIdeal A ^ n) :
    g.val • a - a ∈ maximalIdeal A ^ (n + 1) := by
  have hu : residue A (uniformizerRatio hπ g.val : A) = 1 :=
    congrArg Units.val hg
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  have hc : (uniformizerRatio hπ g.val : A) ^ n * (g.val • b) - b ∈ maximalIdeal A := by
    apply (residue_eq_zero_iff _).mp
    simp only [map_sub, map_mul, map_pow, hu, one_pow, one_mul, residue_inertia_smul,
      sub_self]
  have heq : g.val • (π ^ n * b) - π ^ n * b =
      π ^ n * ((uniformizerRatio hπ g.val : A) ^ n * (g.val • b) - b) := by
    rw [smul_mul', smul_pow', ← uniformizer_mul_ratio hπ g.val, mul_pow]
    ring
  rw [heq, pow_succ]
  exact Ideal.mul_mem_mul
    ((maximalIdeal A).pow_mem_pow (hπ.maximalIdeal_eq ▸ Ideal.subset_span (by simp)) n) hc

/-- Iterating a wild automorphism adds its displacement on the next
graded piece. -/
theorem uniformizerCharacter_ker_pow_smul_sub_mem
    (g : (maximalIdeal A).inertia G) (hg : uniformizerCharacter hπ g = 1)
    (n : ℕ) (a : A) (ha : g.val • a - a ∈ maximalIdeal A ^ n) (k : ℕ) :
    (g.val ^ k) • a - a - k • (g.val • a - a) ∈ maximalIdeal A ^ (n + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : uniformizerCharacter hπ (g ^ k) = 1 := by rw [map_pow, hg, one_pow]
    have hstep := uniformizerCharacter_ker_smul_sub_mem hπ (g ^ k) hk n _ ha
    have heq : (g.val ^ (k + 1)) • a - a - (k + 1) • (g.val • a - a) =
        ((g.val ^ k) • a - a - k • (g.val • a - a)) +
        ((g.val ^ k) • (g.val • a - a) - (g.val • a - a)) := by
      simp only [pow_succ, mul_smul, smul_sub, add_nsmul, one_nsmul]
      abel
    rw [heq]
    exact (maximalIdeal A ^ (n + 1)).add_mem ih hstep

/-- A wild automorphism whose order is a unit in the valuation ring is
trivial. Krull intersection upgrades congruences modulo all ideal powers
to equality. -/
theorem uniformizerCharacter_ker_eq_one_of_pow_eq_one
    [FaithfulSMul G A] (g : (maximalIdeal A).inertia G)
    (hg : uniformizerCharacter hπ g = 1) (q : ℕ) (hq : IsUnit (q : A))
    (hpow : g ^ q = 1) : g = 1 := by
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := A)
  intro a
  have hpow' : g.val ^ q = 1 := congrArg Subtype.val hpow
  have hall : ∀ n : ℕ, g.val • a - a ∈ maximalIdeal A ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hi := uniformizerCharacter_ker_pow_smul_sub_mem hπ g hg n a ih q
      have hm : (q : A) * (g.val • a - a) ∈ maximalIdeal A ^ (n + 1) := by
        simpa only [hpow', one_smul, sub_self, zero_sub, neg_mem_iff, nsmul_eq_mul] using hi
      exact ((maximalIdeal A ^ (n + 1)).unit_mul_mem_iff_mem hq).mp hm
  have hz : g.val • a - a = 0 := by
    apply Ideal.mem_bot.mp
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A)
      (maximalIdeal.isMaximal A).ne_top]
    exact Ideal.mem_iInf.mpr hall
  simpa only [Subgroup.coe_one, one_smul] using sub_eq_zero.mp hz

/-- The kernel of the uniformizer character for a finite faithful action
on a DVR is a group of residue characteristic power order. -/
theorem uniformizerCharacter_ker_isPGroup
    [Finite G] [FaithfulSMul G A] {p : ℕ} (hp : p.Prime)
    [CharP (ResidueField A) p] : IsPGroup p (uniformizerCharacter (G := G) hπ).ker := by
  apply (isPGroup_iff_primeFactors_card_subset hp.ne_zero).mpr
  intro q hq
  obtain ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
  by_cases hpq : p = q
  · subst q
    exact Nat.mem_primeFactors.mpr ⟨hp, dvd_refl p, hp.ne_zero⟩
  · let : Fact q.Prime := ⟨hqp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqdvd
    have hqu : IsUnit (q : A) := by
      by_contra hn
      have hm : (q : A) ∈ maximalIdeal A := hn
      have hz := (residue_eq_zero_iff _).mpr hm
      rw [map_natCast, CharP.cast_eq_zero_iff (ResidueField A) p,
        Nat.prime_dvd_prime_iff_eq hp hqp] at hz
      exact hpq hz
    have hpow : g.val ^ q = 1 := by
      rw [← hg, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
    have hone := uniformizerCharacter_ker_eq_one_of_pow_eq_one hπ g.val g.property q hqu hpow
    have : orderOf g = 1 := orderOf_eq_one_iff.mpr (Subtype.ext hone)
    exact (hqp.ne_one (hg.symm.trans this)).elim

/-- Every prime-to-residue-characteristic finite quotient of inertia for
a finite faithful group of DVR automorphisms is cyclic. -/
theorem isCyclic_inertia_quotient_of_coprime
    [Finite G] [FaithfulSMul G A] {p : ℕ} (hp : p.Prime)
    [CharP (ResidueField A) p] {H : Type*} [Group H] [Finite H]
    (hH : Nat.Coprime p (Nat.card H))
    (f : (maximalIdeal A).inertia G →* H) (hf : Function.Surjective f) : IsCyclic H := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  exact isCyclic_of_residue_character (uniformizerCharacter hπ)
    (uniformizerCharacter_ker_isPGroup hπ hp) hH f hf

end DiscreteValuationRing

/-- An absolute Galois homomorphism with open kernel factors through a
finite Galois extension. The codomain need not be given a topology. -/
theorem exists_finiteGalois_factor_of_isOpen_ker
    {F H : Type*} [Field F] [CharZero F] [Group H]
    (f : Field.absoluteGaloisGroup F →* H)
    (hf : IsOpen (f.ker : Set (Field.absoluteGaloisGroup F))) :
    ∃ (C : IntermediateField F (AlgebraicClosure F))
      (_ : FiniteDimensional F C) (_ : IsGalois F C) (fC : Gal(C/F) →* H),
      ∀ g, fC (AlgEquiv.restrictNormalHom C g) = f g := by
  let D : ClosedSubgroup (Field.absoluteGaloisGroup F) :=
    ⟨f.ker, f.ker.isClosed_of_isOpen hf⟩
  let C := IntermediateField.fixedField D.toSubgroup
  have hfix : C.fixingSubgroup = D.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField D
  let : FiniteDimensional F C := (InfiniteGalois.isOpen_iff_finite C).mp (hfix ▸ hf)
  let : D.Normal := inferInstanceAs f.ker.Normal
  let : IsGalois F C := inferInstance
  let e := (InfiniteGalois.normalAutEquivQuotient D).symm.trans
    (QuotientGroup.quotientKerEquivRange f)
  refine ⟨C, inferInstance, inferInstance, f.range.subtype.comp e.toMonoidHom, fun g ↦ ?_⟩
  change ((QuotientGroup.quotientKerEquivRange f)
    ((InfiniteGalois.normalAutEquivQuotient D).symm
      (AlgEquiv.restrictNormalHom C g))).val = f g
  rw [← InfiniteGalois.normalAutEquivQuotient_apply D g, MulEquiv.symm_apply_apply]
  rfl

section LocalField

open IsLocalRing NumberField

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- Prime-to-residue-characteristic finite quotients of inertia in a
finite local Galois extension are cyclic. -/
theorem isCyclic_finiteLocalInertia_quotient
    (C : IntermediateField (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)))
    [FiniteDimensional (v.adicCompletion K) C] [IsGalois (v.adicCompletion K) C]
    {p : ℕ} (hp : p.Prime) [CharP (ResidueField (v.adicCompletionIntegers K)) p]
    {H : Type*} [Group H] [Finite H] (hH : Nat.Coprime p (Nat.card H))
    (f : (maximalIdeal (IntegralClosure (v.adicCompletionIntegers K) C)).inertia
      Gal(C/v.adicCompletion K) →* H) (hf : Function.Surjective f) : IsCyclic H := by
  let O := v.adicCompletionIntegers K
  let B := IntegralClosure O C
  let : IsFractionRing B C := by
    dsimp only [B]
    delta IntegralClosure
    exact integralClosure.isFractionRing_of_finite_extension (v.adicCompletion K) C
  let : IsDedekindDomain B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.isDedekindDomain O (v.adicCompletion K) C (integralClosure O C)
  have hO : O ≠ ⊤ := by
    intro h
    apply IsDiscreteValuationRing.not_isField O
    exact h ▸ (Subring.topEquiv (R := v.adicCompletion K)).isField
      (Semifield.toIsField (v.adicCompletion K))
  let : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B (not_isField_integralClosure _ hO)).out 3 1).mp
      (inferInstance : IsDedekindDomain B)
  let : SMulDistribClass Gal(C/v.adicCompletion K) B C := ⟨fun g b x ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  let : IsGaloisGroup Gal(C/v.adicCompletion K) O B :=
    IsGaloisGroup.of_isFractionRing Gal(C/v.adicCompletion K) O B (v.adicCompletion K) C
  let : FaithfulSMul Gal(C/v.adicCompletion K) B := IsGaloisGroup.faithful O
  let : CharP (ResidueField B) p :=
    charP_of_injective_ringHom (algebraMap (ResidueField O) (ResidueField B)).injective p
  exact isCyclic_inertia_quotient_of_coprime hp hH f hf

/-- A finite image of local absolute inertia with order prime to the
residue characteristic is cyclic, provided the action has open kernel. -/
theorem isCyclic_localInertia_image_of_coprime
    {p : ℕ} (hp : p.Prime) [CharP (ResidueField (v.adicCompletionIntegers K)) p]
    {H : Type*} [Group H] [Finite H]
    (f : Field.absoluteGaloisGroup (v.adicCompletion K) →* H)
    (hf : IsOpen (f.ker : Set (Field.absoluteGaloisGroup (v.adicCompletion K))))
    (hI : Nat.Coprime p (Nat.card ((localInertiaGroup v).map f))) :
    IsCyclic ((localInertiaGroup v).map f) := by
  obtain ⟨C, hCfin, hCgal, fC, hC⟩ := exists_finiteGalois_factor_of_isOpen_ker f hf
  let J := (maximalIdeal (IntegralClosure (v.adicCompletionIntegers K) C)).inertia
    Gal(C/v.adicCompletion K)
  let fJ := fC.comp J.subtype
  have hrange : fJ.range = (localInertiaGroup v).map f := by
    change (fC.comp J.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    dsimp only [J]
    rw [← map_localInertiaGroup_eq_inertia v C, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext hC
  have hcard : Nat.Coprime p (Nat.card fJ.range) := hrange ▸ hI
  have hcyc : IsCyclic fJ.range :=
    isCyclic_finiteLocalInertia_quotient v C hp hcard fJ.rangeRestrict fJ.rangeRestrict_surjective
  exact hrange ▸ hcyc

end LocalField

section ResidualInertia

open Module IsLocalRing

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

/-- The residue field of the rational completion at two has characteristic two. -/
theorem residueField_twoAdicPlace_charP :
    CharP (ResidueField (twoAdicPlace.adicCompletionIntegers ℚ)) 2 := by
  obtain ⟨_, e, _⟩ := exists_completionTwoEquiv
  let e' := (ResidueField.mapEquiv e).trans (PadicInt.residueField (p := 2))
  exact e'.toRingHom.charP e'.injective 2

/-- The module topology over a discrete coefficient ring is discrete. -/
theorem moduleTopology_eq_bot_of_discrete
    {R M : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    [AddCommGroup M] [Module R M] : moduleTopology R M = ⊥ := by
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  let : ContinuousSMul R M := ⟨continuous_of_discreteTopology⟩
  let : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
  exact le_bot_iff.mp (moduleTopology_le R M)

/-- Finite discrete residual square-zero inertia at two is cyclic. The
wild 2-group is killed by the 3-group image, and tame inertia is cyclic. -/
theorem inertiaTwoImage_isCyclic
    {R W : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    [AddCommGroup W] [Module R W] [Finite W] (ρ : GaloisRep ℚ R W)
    (hkill : ∀ w : W, (3 : ℕ) • w = 0)
    (hunip : ∀ σ ∈ localInertiaGroup twoAdicPlace,
      (ρ.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ - 1) ^ 2 = 0) :
    IsCyclic (inertiaTwoImage ρ) := by
  let : TopologicalSpace (Module.End R W) := moduleTopology R (Module.End R W)
  let : DiscreteTopology (Module.End R W) := ⟨moduleTopology_eq_bot_of_discrete⟩
  let : Finite (Module.End R W) := Finite.of_injective
    (fun f : Module.End R W ↦ (f : W → W)) DFunLike.coe_injective
  let : CharP (ResidueField (twoAdicPlace.adicCompletionIntegers ℚ)) 2 :=
    residueField_twoAdicPlace_charP
  let ρ₂ := ρ.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ))
  let f := ρ₂.toMonoidHom.toHomUnits
  have hf : IsOpen
      (f.ker : Set (Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ))) := by
    change IsOpen (ρ₂.toMonoidHom.toHomUnits.ker :
      Set (Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ)))
    rw [MonoidHom.ker_toHomUnits]
    exact (isOpen_discrete ({1} : Set (Module.End R W))).preimage ρ₂.continuous
  have himage : (localInertiaGroup twoAdicPlace).map f = inertiaTwoImage ρ := by
    change (localInertiaGroup twoAdicPlace).map f =
      (f.comp (localInertiaGroup twoAdicPlace).subtype).range
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.Coprime 2 (Nat.card (inertiaTwoImage ρ)) := by
    obtain ⟨n, hn⟩ := (inertiaTwoImage_isThreeGroup ρ hkill hunip).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  have hcyc := isCyclic_localInertia_image_of_coprime twoAdicPlace (by decide : Nat.Prime 2)
    f hf (himage.symm ▸ hcard)
  exact himage ▸ hcyc

/-- The ramification order of a finite discrete module killed by three,
with square-zero inertia at two, divides three. -/
theorem ramification_two_dvd_three
    {R W : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    [AddCommGroup W] [Module R W] [Finite W] (ρ : GaloisRep ℚ R W)
    (hkill : ∀ w : W, (3 : ℕ) • w = 0)
    (hunip : ∀ σ ∈ localInertiaGroup twoAdicPlace,
      (ρ.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ - 1) ^ 2 = 0) :
    e_two ρ ∣ 3 := by
  let : IsCyclic (inertiaTwoImage ρ) := inertiaTwoImage_isCyclic ρ hkill hunip
  exact ramification_two_dvd_three_of_isCyclic ρ hkill hunip

/-- In particular, a residual hardly ramified representation over a finite
discrete field of characteristic three has inertia order at two dividing three. -/
theorem ramification_two_dvd_three_of_hardlyRamified
    {k V : Type*} [Field k] [Finite k] [CharP k 3]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k] [Algebra ℤ_[3] k]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    (hdim : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hdim ρ) :
    e_two ρ ∣ 3 := by
  let : Finite V := Module.finite_of_finite k
  apply ramification_two_dvd_three ρ
  · intro v
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k 3, zero_smul]
  · exact inertia_two_sq_zero hdim ρ hρ

end ResidualInertia

end ThreeAdicPlan
