/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.FirstRamificationPGroup

/-!
# The finite tame quotient

The residue of the uniformizer ratio is a multiplicative character on inertia.
Its kernel is first ramification and its image has order prime to the residue
characteristic.
-/

@[expose] public section

open IsLocalRing

namespace LocalRamification

variable (R G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Group G] [MulSemiringAction G R]

/-- The unit expressing the ratio of an automorphic uniformizer to itself. -/
noncomputable def uniformizerRatio {π : R} (hπ : Irreducible π) (σ : G) : Rˣ :=
  Classical.choose (IsDiscreteValuationRing.associated_of_irreducible R hπ
    (hπ.map (MulSemiringAction.toRingAut G R σ)))

/-- The chosen unit is the actual uniformizer ratio. -/
theorem uniformizerRatio_spec {π : R} (hπ : Irreducible π) (σ : G) :
    π * (uniformizerRatio R G hπ σ : R) = σ • π :=
  Classical.choose_spec (IsDiscreteValuationRing.associated_of_irreducible R hπ
    (hπ.map (MulSemiringAction.toRingAut G R σ)))

/-- Inertia fixes residues of all integers. -/
theorem inertia_residue_smul (σ : ramificationGroup R G 0) (x : R) :
    residue R (σ.1 • x) = residue R x := by
  apply sub_eq_zero.mp
  rw [← map_sub, residue_eq_zero_iff]
  simpa [ramificationGroup] using σ.2 x

/-- The tame character, with convention sigma(pi)/pi. -/
noncomputable def finiteTameCharacter {π : R} (hπ : Irreducible π) :
    ramificationGroup R G 0 →* (ResidueField R)ˣ where
  toFun σ := Units.map (residue R).toMonoidHom (uniformizerRatio R G hπ σ.1)
  map_one' := by
    have h : uniformizerRatio R G hπ 1 = 1 := by
      apply Units.ext
      apply mul_left_cancel₀ hπ.ne_zero
      simpa using uniformizerRatio_spec R G hπ 1
    simp [h]
  map_mul' σ τ := by
    apply Units.ext
    change residue R (uniformizerRatio R G hπ (σ.1 * τ.1) : R) = _
    have h : (uniformizerRatio R G hπ (σ.1 * τ.1) : R) =
        (uniformizerRatio R G hπ σ.1 : R) * σ.1 • (uniformizerRatio R G hπ τ.1 : R) := by
      apply mul_left_cancel₀ hπ.ne_zero
      rw [uniformizerRatio_spec, mul_smul, ← uniformizerRatio_spec R G hπ τ.1,
        smul_mul', ← uniformizerRatio_spec R G hπ σ.1, mul_assoc]
    rw [h, map_mul, inertia_residue_smul]
    rfl

/-- The kernel condition is exactly the first uniformizer congruence. -/
theorem finiteTameCharacter_eq_one_iff {π : R} (hπ : Irreducible π)
    (σ : ramificationGroup R G 0) :
    finiteTameCharacter R G hπ σ = 1 ↔ σ.1 • π - π ∈ maximalIdeal R ^ 2 := by
  rw [Units.ext_iff]
  change residue R (uniformizerRatio R G hπ σ.1 : R) = 1 ↔ _
  rw [← sub_eq_zero, ← map_one (residue R), ← map_sub, residue_eq_zero_iff,
    hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, ← uniformizerRatio_spec R G hπ, ← mul_sub_one, pow_two]
  exact (mul_dvd_mul_iff_left hπ.ne_zero).symm

/-- Over a finite residue field the tame kernel is exactly first ramification. -/
theorem finiteTameCharacter_ker [Finite (ResidueField R)] {π : R} (hπ : Irreducible π) :
    (finiteTameCharacter R G hπ).ker =
      (firstGroup R G).comap (ramificationGroup R G 0).subtype := by
  ext σ
  exact (finiteTameCharacter_eq_one_iff R G hπ σ).trans
    (mem_next_iff_uniformizer R G hπ 0 σ).symm

/-- The tame quotient embeds into the multiplicative residue field. -/
noncomputable def finiteTameQuotientEmbedding [Finite (ResidueField R)]
    {π : R} (hπ : Irreducible π) :
    ramificationGroup R G 0 ⧸ (firstGroup R G).comap (ramificationGroup R G 0).subtype →*
      (ResidueField R)ˣ :=
  QuotientGroup.lift _ (finiteTameCharacter R G hπ) (by rw [finiteTameCharacter_ker])

/-- The tame quotient map has no remaining kernel. -/
theorem finiteTameQuotientEmbedding_injective [Finite (ResidueField R)]
    {π : R} (hπ : Irreducible π) :
    Function.Injective (finiteTameQuotientEmbedding R G hπ) := by
  intro a b
  refine Quotient.inductionOn₂' a b fun a b h ↦ ?_
  change finiteTameCharacter R G hπ a = finiteTameCharacter R G hπ b at h
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply, ← finiteTameCharacter_ker R G hπ]
  change finiteTameCharacter R G hπ (a⁻¹ * b) = 1
  rw [map_mul, map_inv, h, inv_mul_cancel]

/-- Multiplicative residue units have order prime to the characteristic. -/
theorem residue_units_card_coprime [Finite (ResidueField R)] (p : ℕ)
    [CharP (ResidueField R) p] : (Nat.card (ResidueField R)ˣ).Coprime p := by
  let := Fintype.ofFinite (ResidueField R)
  obtain ⟨n, hp, hn⟩ := FiniteField.card (ResidueField R) p
  rw [Nat.card_units, Nat.card_eq_fintype_card, hn, Nat.coprime_comm,
    hp.coprime_iff_not_dvd]
  intro h
  have hpow : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.ne_zero
  have hone := Nat.dvd_sub hpow h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at hone
  exact hp.not_dvd_one hone

/-- The finite image of the tame character has prime-to-characteristic order. -/
theorem finiteTameCharacter_card_coprime [Finite (ResidueField R)]
    {π : R} (hπ : Irreducible π) (p : ℕ) [CharP (ResidueField R) p] :
    (Nat.card (finiteTameCharacter R G hπ).range).Coprime p :=
  (residue_units_card_coprime R p).of_dvd_left (Subgroup.card_subgroup_dvd_card _)

/-- The inertia quotient by first ramification has prime-to-characteristic order. -/
theorem finiteTameQuotient_card_coprime [Finite (ResidueField R)]
    (p : ℕ) [CharP (ResidueField R) p] :
    (Nat.card (ramificationGroup R G 0 ⧸
      (firstGroup R G).comap (ramificationGroup R G 0).subtype)).Coprime p := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact (residue_units_card_coprime R p).of_dvd_left
    (Subgroup.card_dvd_of_injective (finiteTameQuotientEmbedding R G hπ)
      (finiteTameQuotientEmbedding_injective R G hπ))

open NumberField
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Γ" => Field.absoluteGaloisGroup Kv

/-- The fixed field of an open normal subgroup is finite over the completion. -/
theorem finiteLevel_finiteDimensional (N : OpenNormalSubgroup Γ) :
    FiniteDimensional Kv (IntermediateField.fixedField N.1.1) := by
  rw [← InfiniteGalois.isOpen_iff_finite,
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup Γ)]
  exact N.isOpen'

attribute [local instance] finiteLevel_finiteDimensional

set_option synthInstance.maxHeartbeats 100000 in
-- Integral closure instances require additional elaboration time.
/-- The integral closure at a finite level is a DVR. -/
theorem finiteLevel_isDVR (N : OpenNormalSubgroup Γ) :
    IsDiscreteValuationRing (IntegralClosure O (IntermediateField.fixedField N.1.1)) := by
  let L := IntermediateField.fixedField N.1.1
  let D := IntegralClosure O L
  let : IsDedekindDomain D := by
    change IsDedekindDomain (integralClosure O L)
    exact IsIntegralClosure.isDedekindDomain O Kv L (integralClosure O L)
  let : (maximalIdeal D).LiesOver (maximalIdeal O) := inferInstance
  refine { not_a_field' := ?_ }
  exact Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field O) (maximalIdeal D)

attribute [local instance] finiteLevel_isDVR

set_option synthInstance.maxHeartbeats 100000 in
-- Integral closure instances require additional elaboration time.
/-- Residues at finite Galois levels are finite fields. -/
theorem finiteLevel_residue_finite (N : OpenNormalSubgroup Γ) :
    Finite (ResidueField (IntegralClosure O (IntermediateField.fixedField N.1.1))) := by
  let L := IntermediateField.fixedField N.1.1
  let D := IntegralClosure O L
  let : Module.Finite O D := by
    change Module.Finite O (integralClosure O L)
    exact IsIntegralClosure.finite O Kv L (integralClosure O L)
  let : Ring.HasFiniteQuotients O := {
    finiteQuotient := by
      intro I hI
      obtain ⟨n, rfl⟩ := exists_maximalIdeal_pow_eq_of_principal O
        (IsPrincipalIdealRing.principal (maximalIdeal O)) I hI
      exact
        IsLocalRing.instFiniteQuotientIdealHPowNatMaximalIdealOfIsNoetherianRingOfResidueField n }
  let : Ring.HasFiniteQuotients D := Ring.HasFiniteQuotients.of_module_finite O D
  exact Ring.HasFiniteQuotients.finiteQuotient (IsDiscreteValuationRing.not_a_field D)

attribute [local instance] finiteLevel_residue_finite

set_option maxHeartbeats 1000000 in
-- Integral closure and residue characteristic instances need an extended budget.
set_option synthInstance.maxHeartbeats 100000 in
/-- At every finite Galois level, the tame quotient has order prime to p. -/
theorem finiteLevel_tame_card_coprime (N : OpenNormalSubgroup Γ)
    (p : ℕ) [CharP (ResidueField O) p] :
    (Nat.card (ramificationGroup
      (IntegralClosure O (IntermediateField.fixedField N.1.1))
      Gal(IntermediateField.fixedField N.1.1/Kv) 0 ⧸
      (firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
        Gal(IntermediateField.fixedField N.1.1/Kv)).comap
      (ramificationGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
        Gal(IntermediateField.fixedField N.1.1/Kv) 0).subtype)).Coprime p := by
  let D := IntegralClosure O (IntermediateField.fixedField N.1.1)
  let : CharP (ResidueField D) p :=
    charP_of_injective_ringHom (ResidueField.map (algebraMap O D)).injective p
  exact finiteTameQuotient_card_coprime D _ p

end LocalRamification
