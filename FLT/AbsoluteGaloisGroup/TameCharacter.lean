/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The level-one tame character

For a finite place `v`, this file constructs the level-one tame character on local inertia.
Choose a uniformizer `pi` and a `(q - 1)`-st root `alpha` of it.  For `sigma` in inertia, the
Kummer ratio `sigma(alpha) / alpha` is integral and a root of unity.  Reducing it modulo the
maximal ideal is multiplicative because inertia acts trivially on the residue field.  The roots
of unity obtained this way are identified with the units of the original residue field through
the canonical residue-field inclusion.

The construction does not use `localTameAbelianInertiaGroup`.  We also prove that changing the
uniformizer and its root does not change the reduced character, and isolate the degenerate
residue-cardinality-two case.
-/

@[expose] public section

open NumberField

variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "ᵐ" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "ᵊaᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation "Aᵥ" => IntegralClosure ᵊaᵥ (Kᵥᵃˡᵍ)

attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubring_fLT IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal
  mulSemiringActionIntegralClosure
  Subalgebra.algebra
  CommRing.toCommSemiring

/-- The local inertia group is closed in the Krull topology. -/
lemma localInertiaGroup_isClosed :
    IsClosed (localInertiaGroup v : Set (Γ Kᵥ)) where
  isOpen_compl := isOpen_iff_mem_nhds.mpr fun σ hσ ↦ by
    rw [Set.mem_compl_iff, SetLike.mem_coe, localInertiaGroup,
      AddSubgroup.mem_inertia] at hσ
    push Not at hσ
    obtain ⟨x, hx⟩ := hσ
    refine mem_nhds_iff.mpr ⟨{τ | τ • x = σ • x}, ?_, ?_, rfl⟩
    · intro τ hτ
      rw [Set.mem_compl_iff, SetLike.mem_coe, localInertiaGroup,
        AddSubgroup.mem_inertia]
      push Not
      refine ⟨x, ?_⟩
      change τ • x = σ • x at hτ
      rw [hτ]
      exact hx
    · exact ContinuousSMulDiscrete.isOpen_smul_eq _ x (σ • x)

open IntermediateField in
/-- The subgroup used by the deformation-theory API is contained in local inertia. -/
lemma localTameAbelianInertiaGroup_le_localInertiaGroup :
    localTameAbelianInertiaGroup v ≤ localInertiaGroup v := by
  intro σ hσ
  have hfix : σ ∈ (fixedField (localInertiaGroup v)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hσ x (pow_mem hx _)
  have heq : (fixedField (localInertiaGroup v)).fixingSubgroup = localInertiaGroup v :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨localInertiaGroup v, localInertiaGroup_isClosed v⟩ : ClosedSubgroup (Γ Kᵥ))
  exact heq ▸ hfix

lemma residueCard_one_lt : 1 < Nat.card (κ ᵊaᵥ) :=
  Finite.one_lt_card_iff_nontrivial.mpr inferInstance

lemma tameDegree_pos : 0 < Nat.card (κ ᵊaᵥ) - 1 := by
  have := residueCard_one_lt v
  omega

noncomputable instance tameDegree_neZero :
    NeZero (Nat.card (κ ᵊaᵥ) - 1) := ⟨(tameDegree_pos v).ne'⟩

noncomputable def tameUniformizer : ᵊaᵥ :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer K v).choose

lemma tameUniformizer_spec :
    Valued.v (tameUniformizer v).1 = Multiplicative.ofAdd (-1 : ℤ) :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer K v).choose_spec

lemma tameUniformizer_ne_zero : tameUniformizer v ≠ 0 :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
    (tameUniformizer_spec v)

noncomputable def tameUniformizerRoot : Kᵥᵃˡᵍ :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v).1)
    (tameDegree_pos v)).choose

lemma tameUniformizerRoot_spec :
    tameUniformizerRoot v ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v).1 :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v).1)
    (tameDegree_pos v)).choose_spec

lemma tameUniformizerRoot_ne_zero : tameUniformizerRoot v ≠ 0 := by
  intro h
  have hpow := tameUniformizerRoot_spec v
  rw [h, zero_pow (tameDegree_pos v).ne'] at hpow
  apply tameUniformizer_ne_zero v
  apply Subtype.ext
  apply (algebraMap Kᵥ (Kᵥᵃˡᵍ)).injective
  simpa using hpow.symm

noncomputable def kummerRatio (σ : localInertiaGroup v) : Kᵥᵃˡᵍ :=
  σ.1 (tameUniformizerRoot v) / tameUniformizerRoot v

lemma kummerRatio_pow (σ : localInertiaGroup v) :
    kummerRatio v σ ^ (Nat.card (κ ᵊaᵥ) - 1) = 1 := by
  rw [kummerRatio, div_pow, ← map_pow, tameUniformizerRoot_spec,
    AlgEquiv.commutes, div_self]
  exact (map_ne_zero (algebraMap Kᵥ (Kᵥᵃˡᵍ))).mpr fun h ↦
    tameUniformizer_ne_zero v (Subtype.ext h)

noncomputable def kummerRatioIntegral (σ : localInertiaGroup v) : Aᵥ :=
  ⟨kummerRatio v σ, IsIntegral.of_pow (tameDegree_pos v)
    (by rw [kummerRatio_pow]; exact isIntegral_one)⟩

lemma kummerRatioIntegral_pow (σ : localInertiaGroup v) :
    kummerRatioIntegral v σ ^ (Nat.card (κ ᵊaᵥ) - 1) = 1 := by
  apply Subtype.ext
  exact kummerRatio_pow v σ

lemma root_ne_of_pow_eq_uniformizer {pi : ᵊaᵥ} (hpi : pi ≠ 0)
    {alpha : Kᵥᵃˡᵍ}
    (halpha : alpha ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) pi.1) : alpha ≠ 0 := by
  intro h
  rw [h, zero_pow (tameDegree_pos v).ne'] at halpha
  apply hpi
  apply Subtype.ext
  apply (algebraMap Kᵥ (Kᵥᵃˡᵍ)).injective
  simpa using halpha.symm

lemma kummerRatioOfRoot_pow {pi : ᵊaᵥ} (hpi : pi ≠ 0)
    {alpha : Kᵥᵃˡᵍ}
    (halpha : alpha ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) pi.1)
    (σ : localInertiaGroup v) :
    (σ.1 alpha / alpha) ^ (Nat.card (κ ᵊaᵥ) - 1) = 1 := by
  rw [div_pow, ← map_pow, halpha, AlgEquiv.commutes, div_self]
  exact (map_ne_zero (algebraMap Kᵥ (Kᵥᵃˡᵍ))).mpr fun h ↦
    hpi (Subtype.ext h)

noncomputable def kummerRatioIntegralOfRoot {pi : ᵊaᵥ} (hpi : pi ≠ 0)
    {alpha : Kᵥᵃˡᵍ}
    (halpha : alpha ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) pi.1)
    (σ : localInertiaGroup v) : Aᵥ :=
  ⟨σ.1 alpha / alpha, IsIntegral.of_pow (tameDegree_pos v)
    (by rw [kummerRatioOfRoot_pow v hpi halpha σ]; exact isIntegral_one)⟩

lemma kummerRatioIntegralOfRoot_pow {pi : ᵊaᵥ} (hpi : pi ≠ 0)
    {alpha : Kᵥᵃˡᵍ}
    (halpha : alpha ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) pi.1)
    (σ : localInertiaGroup v) :
    kummerRatioIntegralOfRoot v hpi halpha σ ^
      (Nat.card (κ ᵊaᵥ) - 1) = 1 := by
  apply Subtype.ext
  exact kummerRatioOfRoot_pow v hpi halpha σ

noncomputable def reducedKummerRatioOfRoot {pi : ᵊaᵥ} (hpi : pi ≠ 0)
    {alpha : Kᵥᵃˡᵍ}
    (halpha : alpha ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) pi.1)
    (σ : localInertiaGroup v) :
    rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ) :=
  rootsOfUnity.mkOfPowEq
    (IsLocalRing.residue Aᵥ (kummerRatioIntegralOfRoot v hpi halpha σ)) <| by
      rw [← map_pow, kummerRatioIntegralOfRoot_pow, map_one]

lemma exists_unit_root_ratio_of_uniformizers
    {pi pi' : ᵊaᵥ}
    (hpi : Valued.v pi.1 = Multiplicative.ofAdd (-1 : ℤ))
    (hpi' : Valued.v pi'.1 = Multiplicative.ofAdd (-1 : ℤ))
    {alpha beta : Kᵥᵃˡᵍ}
    (halpha : alpha ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) pi.1)
    (hbeta : beta ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) pi'.1) :
    ∃ z : Aᵥˣ, (z : Aᵥ).1 = beta / alpha := by
  have hne : pi ≠ 0 :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hpi
  have hne' : pi' ≠ 0 :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hpi'
  have hassoc : Associated pi pi' := Ideal.span_singleton_eq_span_singleton.mp <|
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
      K v hpi).symm.trans
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
      K v hpi')
  obtain ⟨u, hu⟩ := hassoc
  have huval : pi.1 * (u : ᵊaᵥ).1 = pi'.1 := congrArg Subtype.val hu
  have hzpow : (beta / alpha) ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap ᵊaᵥ (Kᵥᵃˡᵍ) (u : ᵊaᵥ) := by
    rw [div_pow, hbeta, halpha, ← huval, map_mul]
    rw [mul_div_cancel_left₀]
    · exact (IsScalarTower.algebraMap_apply ᵊaᵥ Kᵥ (Kᵥᵃˡᵍ) (u : ᵊaᵥ)).symm
    · exact (map_ne_zero (algebraMap Kᵥ (Kᵥᵃˡᵍ))).mpr fun h ↦ hne (Subtype.ext h)
  let z : Aᵥ := ⟨beta / alpha, IsIntegral.of_pow (tameDegree_pos v) <| by
    rw [hzpow]
    exact isIntegral_algebraMap⟩
  have hzpowA : z ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap ᵊaᵥ Aᵥ (u : ᵊaᵥ) := by
    apply Subtype.ext
    exact hzpow.trans (IsScalarTower.algebraMap_apply ᵊaᵥ Aᵥ (Kᵥᵃˡᵍ) (u : ᵊaᵥ))
  have hzunit : IsUnit z := (isUnit_pow_iff (tameDegree_pos v).ne').mp <| by
    rw [hzpowA]
    exact IsUnit.map (algebraMap ᵊaᵥ Aᵥ) u.isUnit
  refine ⟨hzunit.unit, ?_⟩
  rw [hzunit.unit_spec]

noncomputable def reducedKummerRatio (σ : localInertiaGroup v) :
    rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ) :=
  rootsOfUnity.mkOfPowEq
    (IsLocalRing.residue Aᵥ (kummerRatioIntegral v σ)) <| by
      rw [← map_pow, kummerRatioIntegral_pow, map_one]

lemma kummerRatioIntegral_mul (σ τ : localInertiaGroup v) :
    kummerRatioIntegral v (σ * τ) =
      (σ.1 • kummerRatioIntegral v τ) * kummerRatioIntegral v σ := by
  apply Subtype.ext
  change (σ.1 * τ.1) (tameUniformizerRoot v) / tameUniformizerRoot v =
    σ.1 (τ.1 (tameUniformizerRoot v) / tameUniformizerRoot v) *
      (σ.1 (tameUniformizerRoot v) / tameUniformizerRoot v)
  rw [AlgEquiv.mul_apply, map_div₀]
  field_simp [tameUniformizerRoot_ne_zero v]

lemma residue_smul_eq (σ : localInertiaGroup v) (x : Aᵥ) :
    IsLocalRing.residue Aᵥ (σ.1 • x) = IsLocalRing.residue Aᵥ x := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  exact σ.2 x

lemma reducedKummerRatio_mul (σ τ : localInertiaGroup v) :
    reducedKummerRatio v (σ * τ) =
      reducedKummerRatio v σ * reducedKummerRatio v τ := by
  apply rootsOfUnity.coe_injective
  simp only [reducedKummerRatio, rootsOfUnity.coe_mkOfPowEq,
    kummerRatioIntegral_mul, map_mul, residue_smul_eq]
  exact mul_comm _ _

noncomputable def reducedKummerCharacter :
    localInertiaGroup v →* rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ) where
  toFun := reducedKummerRatio v
  map_one' := by
    apply rootsOfUnity.coe_injective
    simp only [reducedKummerRatio, rootsOfUnity.coe_mkOfPowEq]
    have hr : kummerRatioIntegral v 1 = 1 := by
      apply Subtype.ext
      exact div_self (tameUniformizerRoot_ne_zero v)
    simp [hr]
  map_mul' := reducedKummerRatio_mul v

lemma reducedKummerRatio_uniformizer_independent
    {pi : ᵊaᵥ}
    (hpi : Valued.v pi.1 = Multiplicative.ofAdd (-1 : ℤ))
    {beta : Kᵥᵃˡᵍ}
    (hbeta : beta ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) pi.1)
    (σ : localInertiaGroup v) :
    reducedKummerRatioOfRoot v
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hpi) hbeta σ =
      reducedKummerRatio v σ := by
  obtain ⟨z, hz⟩ := exists_unit_root_ratio_of_uniformizers (v := v)
    (tameUniformizer_spec v) hpi (tameUniformizerRoot_spec v) hbeta
  have hzinv : ((z⁻¹ : Aᵥˣ) : Aᵥ).1 = (beta / tameUniformizerRoot v)⁻¹ := by
    calc
      ((z⁻¹ : Aᵥˣ) : Aᵥ).1 = ((z : Aᵥ).1)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        exact congrArg (fun x : Aᵥ ↦ x.1) (Units.mul_inv z)
      _ = (beta / tameUniformizerRoot v)⁻¹ := congrArg Inv.inv hz
  have hratio : kummerRatioIntegralOfRoot v
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hpi) hbeta σ =
      (σ.1 • (z : Aᵥ)) * ((z⁻¹ : Aᵥˣ) : Aᵥ) * kummerRatioIntegral v σ := by
    apply Subtype.ext
    change σ.1 beta / beta =
      σ.1 (z : Aᵥ).1 * ((z⁻¹ : Aᵥˣ) : Aᵥ).1 *
        (σ.1 (tameUniformizerRoot v) / tameUniformizerRoot v)
    rw [hz, hzinv]
    simp only [map_div₀]
    field_simp [tameUniformizerRoot_ne_zero v,
      root_ne_of_pow_eq_uniformizer v
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hpi) hbeta]
  apply rootsOfUnity.coe_injective
  simp only [reducedKummerRatioOfRoot, reducedKummerRatio,
    rootsOfUnity.coe_mkOfPowEq, hratio, map_mul, residue_smul_eq]
  rw [← map_mul, Units.mul_inv, map_one, one_mul]

noncomputable def residueFieldMap : κ ᵊaᵥ →+* κ Aᵥ :=
  IsLocalRing.ResidueField.map (algebraMap ᵊaᵥ Aᵥ)

lemma tameDegree_cast_ne_zero :
    (Nat.card (κ ᵊaᵥ) - 1 : κ Aᵥ) ≠ 0 := by
  let _ := Fintype.ofFinite (κ ᵊaᵥ)
  intro h
  have hbase : (Nat.card (κ ᵊaᵥ) - 1 : κ ᵊaᵥ) = 0 := by
    apply (residueFieldMap v).injective
    rw [map_sub, map_natCast, map_one, map_zero]
    exact h
  have hcast : (Nat.card (κ ᵊaᵥ) - 1 : κ ᵊaᵥ) = -1 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_card_eq_zero]
    simp
  rw [hcast] at hbase
  exact (neg_ne_zero.mpr one_ne_zero) hbase

lemma eq_one_of_pow_eq_one_of_sub_mem
    {x : Aᵥ} (hpow : x ^ (Nat.card (κ ᵊaᵥ) - 1) = 1)
    (hmod : x - 1 ∈ ᵐ Aᵥ) : x = 1 := by
  have hres : IsLocalRing.residue Aᵥ x = 1 := by
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem x 1).mpr hmod
  have hprod : (∑ i ∈ Finset.range (Nat.card (κ ᵊaᵥ) - 1), x ^ i) * (x - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  rcases mul_eq_zero.mp hprod with hsum | hx
  · apply False.elim
    apply tameDegree_cast_ne_zero v
    calc
      (Nat.card (κ ᵊaᵥ) - 1 : κ Aᵥ) =
          ∑ i ∈ Finset.range (Nat.card (κ ᵊaᵥ) - 1), (1 : κ Aᵥ) ^ i := by simp
      _ = IsLocalRing.residue Aᵥ
          (∑ i ∈ Finset.range (Nat.card (κ ᵊaᵥ) - 1), x ^ i) := by
            simp [hres]
      _ = 0 := by rw [hsum, map_zero]
  · exact sub_eq_zero.mp hx

noncomputable def residueUnitsToRootsOfUnity :
    (κ ᵊaᵥ)ˣ →* rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ) :=
  MonoidHom.codRestrict (Units.map (residueFieldMap v).toMonoidHom)
    (rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ)) fun x ↦ by
      rw [mem_rootsOfUnity, ← map_pow, ← Nat.card_units]
      exact congrArg (Units.map (residueFieldMap v).toMonoidHom) pow_card_eq_one'

lemma residueUnitsToRootsOfUnity_injective :
    Function.Injective (residueUnitsToRootsOfUnity v) := by
  intro x y hxy
  apply Units.map_injective (residueFieldMap v).injective
  exact congrArg Subtype.val hxy

lemma residueRoots_natCard :
    Nat.card (rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ)) =
      Nat.card (κ ᵊaᵥ) - 1 := by
  apply le_antisymm (card_rootsOfUnity _ _)
  calc
    Nat.card (κ ᵊaᵥ) - 1 = Nat.card (κ ᵊaᵥ)ˣ := (Nat.card_units _).symm
    _ ≤ Nat.card (rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ)) :=
      Nat.card_le_card_of_injective (residueUnitsToRootsOfUnity v)
        (residueUnitsToRootsOfUnity_injective v)

noncomputable def residueUnitsEquivRoots :
    (κ ᵊaᵥ)ˣ ≃* rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ) :=
  MulEquiv.ofBijective (residueUnitsToRootsOfUnity v) <|
    (Nat.bijective_iff_injective_and_card _).mpr ⟨
      residueUnitsToRootsOfUnity_injective v,
      (Nat.card_units _).trans (residueRoots_natCard v).symm⟩

noncomputable def tameCharacter : localInertiaGroup v →* (κ ᵊaᵥ)ˣ :=
  (residueUnitsEquivRoots v).symm.toMonoidHom.comp (reducedKummerCharacter v)

lemma tameCharacter_uniformizer_independent
    {pi : ᵊaᵥ}
    (hpi : Valued.v pi.1 = Multiplicative.ofAdd (-1 : ℤ))
    {beta : Kᵥᵃˡᵍ}
    (hbeta : beta ^ (Nat.card (κ ᵊaᵥ) - 1) =
      algebraMap Kᵥ (Kᵥᵃˡᵍ) pi.1)
    (σ : localInertiaGroup v) :
    tameCharacter v σ = (residueUnitsEquivRoots v).symm
      (reducedKummerRatioOfRoot v
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hpi) hbeta σ) := by
  change (residueUnitsEquivRoots v).symm (reducedKummerRatio v σ) = _
  rw [reducedKummerRatio_uniformizer_independent v hpi hbeta σ]

lemma tameCharacter_eq_one_iff (σ : localInertiaGroup v) :
    tameCharacter v σ = 1 ↔
      σ.1 (tameUniformizerRoot v) = tameUniformizerRoot v := by
  constructor
  · intro hσ
    have hraw : reducedKummerCharacter v σ = 1 := by
      apply (residueUnitsEquivRoots v).symm.injective
      simpa [tameCharacter] using hσ
    have hres : IsLocalRing.residue Aᵥ (kummerRatioIntegral v σ) = 1 := by
      have := congrArg (fun z : rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ) ↦
        ((z : (κ Aᵥ)ˣ) : κ Aᵥ)) hraw
      simpa [reducedKummerCharacter, reducedKummerRatio] using this
    have hmod : kummerRatioIntegral v σ - 1 ∈ ᵐ Aᵥ :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hres
    have hr := eq_one_of_pow_eq_one_of_sub_mem (v := v)
      (kummerRatioIntegral_pow v σ) hmod
    have hr' := congrArg Subtype.val hr
    change σ.1 (tameUniformizerRoot v) / tameUniformizerRoot v = 1 at hr'
    exact (div_eq_one_iff_eq (tameUniformizerRoot_ne_zero v)).mp hr'
  · intro hσ
    have hr : kummerRatioIntegral v σ = 1 := by
      apply Subtype.ext
      change σ.1 (tameUniformizerRoot v) / tameUniformizerRoot v = 1
      rw [hσ, div_self (tameUniformizerRoot_ne_zero v)]
    have hraw : reducedKummerCharacter v σ = 1 := by
      apply rootsOfUnity.coe_injective
      simp [reducedKummerCharacter, reducedKummerRatio, hr]
    simp [tameCharacter, hraw]

lemma tameCharacter_eq_one_of_residueCard_eq_two
    (hq : Nat.card (κ ᵊaᵥ) = 2) : tameCharacter v = 1 := by
  have hc : Nat.card (κ ᵊaᵥ)ˣ = 1 := by
    rw [Nat.card_units, hq]
  let _ : Subsingleton (κ ᵊaᵥ)ˣ := (Nat.card_eq_one_iff_unique.mp hc).1
  apply MonoidHom.ext
  intro σ
  exact Subsingleton.elim _ _

open IntermediateField in
/-- The deformation-theory subgroup is contained in the kernel of the tame character. -/
lemma localTameAbelianInertiaGroup_subgroupOf_le_tameCharacter_ker :
    (localTameAbelianInertiaGroup v).subgroupOf (localInertiaGroup v) ≤
      (tameCharacter v).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker, tameCharacter_eq_one_iff]
  exact hσ (tameUniformizerRoot v) <| by
    rw [tameUniformizerRoot_spec]
    exact IntermediateField.algebraMap_mem _ _

/-- The deformation-theory subgroup is the kernel of the independently constructed tame
character. -/
theorem localTameAbelianInertiaGroup_subgroupOf_eq_tameCharacter_ker :
    (localTameAbelianInertiaGroup v).subgroupOf (localInertiaGroup v) =
      (tameCharacter v).ker := by
  sorry
