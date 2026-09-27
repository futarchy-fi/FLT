/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaComparison
public import FLT.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.Topology.Algebra.Valued.LocallyCompact

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
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "ᵊaᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
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

/-- A chosen uniformizer of the completed valuation ring at `v`. -/
noncomputable def tameUniformizer : ᵊaᵥ :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer K v).choose

lemma tameUniformizer_spec :
    Valued.v (tameUniformizer v).1 = Multiplicative.ofAdd (-1 : ℤ) :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer K v).choose_spec

lemma tameUniformizer_ne_zero : tameUniformizer v ≠ 0 :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
    (tameUniformizer_spec v)

/-- A chosen `(q - 1)`-st root of `tameUniformizer` in the algebraic closure. -/
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

/-- The Kummer ratio `σ(α) / α` associated to the chosen uniformizer root. -/
noncomputable def kummerRatio (σ : localInertiaGroup v) : Kᵥᵃˡᵍ :=
  σ.1 (tameUniformizerRoot v) / tameUniformizerRoot v

lemma kummerRatio_pow (σ : localInertiaGroup v) :
    kummerRatio v σ ^ (Nat.card (κ ᵊaᵥ) - 1) = 1 := by
  rw [kummerRatio, div_pow, ← map_pow, tameUniformizerRoot_spec,
    AlgEquiv.commutes, div_self]
  exact (map_ne_zero (algebraMap Kᵥ (Kᵥᵃˡᵍ))).mpr fun h ↦
    tameUniformizer_ne_zero v (Subtype.ext h)

/-- The Kummer ratio regarded as an element of the integral closure. -/
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

/-- The integral Kummer ratio attached to an arbitrary uniformizer root. -/
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

/-- The reduction of an arbitrary integral Kummer ratio as a `(q - 1)`-st root of unity. -/
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

/-- The reduced Kummer ratio attached to the chosen uniformizer root. -/
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

/-- The multiplicative character formed by the reduced Kummer ratios. -/
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

/-- The residue-field map induced by the inclusion into the integral closure. -/
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

/-- The canonical embedding of residue-field units into `(q - 1)`-st roots of unity. -/
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

/-- Residue-field units are equivalent to the `(q - 1)`-st roots of unity upstairs. -/
noncomputable def residueUnitsEquivRoots :
    (κ ᵊaᵥ)ˣ ≃* rootsOfUnity (Nat.card (κ ᵊaᵥ) - 1) (κ Aᵥ) :=
  MulEquiv.ofBijective (residueUnitsToRootsOfUnity v) <|
    (Nat.bijective_iff_injective_and_card _).mpr ⟨
      residueUnitsToRootsOfUnity_injective v,
      (Nat.card_units _).trans (residueRoots_natCard v).symm⟩

/-- The level-one tame character on local inertia. -/
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

private lemma flatOfDedekindOfTorsionFree
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsDedekindDomain R] [Module.IsTorsionFree R M] : Module.Flat R M :=
  inferInstance

private lemma localInertia_fixes_of_isUnit_of_pow_fixed
    {y : Aᵥ} (hy : IsUnit y)
    (hpow : ∀ τ : localInertiaGroup v,
      τ.1 • (y ^ (Nat.card (κ 𝒪ᵥ) - 1)) =
        y ^ (Nat.card (κ 𝒪ᵥ) - 1))
    (σ : localInertiaGroup v) : σ.1 • y = y := by
  let u : Aᵥˣ := hy.unit
  have hu : (u : Aᵥ) = y := hy.unit_spec
  let r : Aᵥ := (σ.1 • y) * (u⁻¹ : Aᵥˣ)
  have hrpow : r ^ (Nat.card (κ 𝒪ᵥ) - 1) = 1 := by
    calc
      r ^ (Nat.card (κ 𝒪ᵥ) - 1) =
          (σ.1 • y) ^ (Nat.card (κ 𝒪ᵥ) - 1) *
            ((u⁻¹ : Aᵥˣ) : Aᵥ) ^ (Nat.card (κ 𝒪ᵥ) - 1) := by
              simp only [r, mul_pow]
      _ = y ^ (Nat.card (κ 𝒪ᵥ) - 1) *
            ((u⁻¹ : Aᵥˣ) : Aᵥ) ^ (Nat.card (κ 𝒪ᵥ) - 1) := by
              have hs : (σ.1 • y) ^ (Nat.card (κ 𝒪ᵥ) - 1) =
                  y ^ (Nat.card (κ 𝒪ᵥ) - 1) := by
                simpa only [smul_pow'] using hpow σ
              rw [hs]
      _ = (y * ((u⁻¹ : Aᵥˣ) : Aᵥ)) ^ (Nat.card (κ 𝒪ᵥ) - 1) := by
              exact (mul_pow _ _ _).symm
      _ = 1 := by rw [← hu, Units.mul_inv, one_pow]
  have hrmod : r - 1 ∈ IsLocalRing.maximalIdeal Aᵥ := by
    rw [show r - 1 = (σ.1 • y - y) * ((u⁻¹ : Aᵥˣ) : Aᵥ) by
      dsimp only [r]
      rw [sub_mul, ← hu, Units.mul_inv]]
    exact Ideal.mul_mem_right _ _ (σ.2 y)
  have hr := eq_one_of_pow_eq_one_of_sub_mem (v := v) hrpow hrmod
  have := congrArg (fun z : Aᵥ ↦ z * y) hr
  simpa [r, ← hu, mul_assoc] using this

set_option maxHeartbeats 1000000 in
-- Synthesizing the integral-closure towers below exceeds the project-wide heartbeat limit.
set_option synthInstance.maxHeartbeats 100000 in
set_option linter.style.haveILetI false in
private lemma finiteInertiaField_ramificationIdx_eq_one
    (L : IntermediateField Kᵥ (Kᵥᵃˡᵍ))
    [FiniteDimensional Kᵥ L] [IsGalois Kᵥ L]
    (E : IntermediateField Kᵥ L)
    [IsInertiaField Kᵥ L (IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵥ L)) E] :
    (IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵥ E)).ramificationIdx 𝒪ᵥ = 1 := by
  let B := IntegralClosure 𝒪ᵥ L
  let P := 𝔪 B
  let H := P.inertia Gal(L/Kᵥ)
  let D := IntegralClosure 𝒪ᵥ E
  let p := 𝔪 𝒪ᵥ
  let q := 𝔪 D
  letI : IsFractionRing B L := by
    dsimp only [B]
    delta IntegralClosure
    exact integralClosure.isFractionRing_of_finite_extension Kᵥ L
  letI : Module.Finite 𝒪ᵥ B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.finite 𝒪ᵥ Kᵥ L (integralClosure 𝒪ᵥ L)
  letI : Module.IsTorsionFree 𝒪ᵥ B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap Kᵥ L).injective
    have hxy' := congrArg Subtype.val hxy
    change (algebraMap Kᵥ L) (x : Kᵥ) = (algebraMap Kᵥ L) (y : Kᵥ) at hxy'
    exact hxy'
  letI : Module.Flat 𝒪ᵥ B := by
    exact @flatOfDedekindOfTorsionFree 𝒪ᵥ B _ _ Algebra.toModule _
      (by exact this)
  letI : IsDedekindDomain B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.isDedekindDomain 𝒪ᵥ Kᵥ L (integralClosure 𝒪ᵥ L)
  letI : P.LiesOver p := by dsimp only [P, p]; infer_instance
  letI : SMulDistribClass Gal(L/Kᵥ) B L := ⟨fun g b l ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  letI : IsGaloisGroup Gal(L/Kᵥ) 𝒪ᵥ B :=
    IsGaloisGroup.of_isFractionRing Gal(L/Kᵥ) 𝒪ᵥ B Kᵥ L
  haveI : IsGaloisGroup H E L := by dsimp only [H, P, B]; infer_instance
  haveI : FiniteDimensional E L := IsGaloisGroup.finiteDimensional H E L
  letI : FaithfulSMul E L := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact (algebraMap E L).injective
  letI : Module.IsTorsionFree E L := .of_smul_eq_zero (by simp)
  haveI : FiniteDimensional Kᵥ E := FiniteDimensional.left Kᵥ E L
  letI : IsFractionRing D E := by
    dsimp only [D]
    change IsFractionRing (integralClosure 𝒪ᵥ E) E
    exact integralClosure.isFractionRing_of_finite_extension Kᵥ E
  letI : Module.Finite 𝒪ᵥ D := by
    dsimp only [D]
    change Module.Finite 𝒪ᵥ (integralClosure 𝒪ᵥ E)
    exact IsIntegralClosure.finite 𝒪ᵥ Kᵥ E (integralClosure 𝒪ᵥ E)
  letI : IsDedekindDomain D := by
    dsimp only [D]
    change IsDedekindDomain (integralClosure 𝒪ᵥ E)
    exact IsIntegralClosure.isDedekindDomain 𝒪ᵥ Kᵥ E (integralClosure 𝒪ᵥ E)
  have hp : p ≠ ⊥ := by
    dsimp only [p]
    exact IsDiscreteValuationRing.not_a_field 𝒪ᵥ
  letI : Ring.HasFiniteQuotients 𝒪ᵥ := {
    finiteQuotient := by
      intro I hI
      obtain ⟨n, rfl⟩ := exists_maximalIdeal_pow_eq_of_principal 𝒪ᵥ
        (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal 𝒪ᵥ)) I hI
      exact
        IsLocalRing.instFiniteQuotientIdealHPowNatMaximalIdealOfIsNoetherianRingOfResidueField n }
  letI : Ring.HasFiniteQuotients D :=
    Ring.HasFiniteQuotients.of_module_finite 𝒪ᵥ D
  letI : q.LiesOver p := by dsimp only [q, p]; infer_instance
  have hq : q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp q
  letI : Finite (D ⧸ q) := Ring.HasFiniteQuotients.finiteQuotient hq
  let eEL : E →ₐ[𝒪ᵥ] L := E.val.restrictScalars 𝒪ᵥ
  letI : Algebra D B := (IntegralClosure.map eEL).toAlgebra
  letI : IsScalarTower 𝒪ᵥ D B := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    rfl
  letI : Algebra D L := (eEL.toRingHom.comp (algebraMap D E)).toAlgebra
  letI : IsScalarTower D E L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower D B L := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    rfl
  letI : Module.IsTorsionFree D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    rw [faithfulSMul_iff_algebraMap_injective]
    exact IntegralClosure.map_injective eEL eEL.injective
  letI : Module.Flat D B := by
    exact @flatOfDedekindOfTorsionFree D B _ _ Algebra.toModule _
      (by exact this)
  letI : FaithfulSMul D B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact IntegralClosure.map_injective eEL eEL.injective
  letI : Module.Finite D B := Module.Finite.of_restrictScalars_finite 𝒪ᵥ D B
  letI : SMulDistribClass H B L := ⟨fun g b l ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  letI : IsGaloisGroup H D B := IsGaloisGroup.of_isFractionRing H D B E L
  letI : P.LiesOver q := by dsimp only [P, q]; infer_instance
  have htop : P.inertia H = ⊤ := by
    change H.subgroupOf H = ⊤
    exact Subgroup.subgroupOf_self H
  have hramD : P.ramificationIdx D = Module.finrank E L := by
    calc
      P.ramificationIdx D = q.ramificationIdxIn B :=
        (Ideal.ramificationIdxIn_eq_ramificationIdx q P H).symm
      _ = Nat.card (P.inertia H) := (Ideal.card_inertia_eq_ramificationIdxIn q P).symm
      _ = Nat.card H := by rw [htop]; simp
      _ = Module.finrank E L := IsGaloisGroup.card_eq_finrank H E L
  have hramO : P.ramificationIdx 𝒪ᵥ = Module.finrank E L := by
    calc
      P.ramificationIdx 𝒪ᵥ = p.ramificationIdxIn B :=
        (Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(L/Kᵥ)).symm
      _ = Nat.card (P.inertia Gal(L/Kᵥ)) :=
        (Ideal.card_inertia_eq_ramificationIdxIn p P).symm
      _ = Module.finrank E L := IsGaloisGroup.card_eq_finrank H E L
  have htower := Ideal.ramificationIdx_tower (R := 𝒪ᵥ) q P
  rw [hramO, hramD] at htower
  have hpos : 0 < Module.finrank E L := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  simpa using htower.symm

set_option maxHeartbeats 1000000 in
-- This combines both finite-level constructions, so typeclass synthesis needs the same budget.
set_option synthInstance.maxHeartbeats 100000 in
set_option linter.style.haveILetI false in
/-- The deformation-theory subgroup is the kernel of the independently constructed tame
character. -/
theorem localTameAbelianInertiaGroup_subgroupOf_eq_tameCharacter_ker :
    (localTameAbelianInertiaGroup v).subgroupOf (localInertiaGroup v) =
      (tameCharacter v).ker := by
  apply le_antisymm
  · exact localTameAbelianInertiaGroup_subgroupOf_le_tameCharacter_ker v
  · intro σ hσ
    change σ.1 ∈ localTameAbelianInertiaGroup v
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hσα : σ.1 (tameUniformizerRoot v) = tameUniformizerRoot v :=
      (tameCharacter_eq_one_iff v σ).mp hσ
    let d := Nat.card (κ 𝒪ᵥ) - 1
    let a : Kᵥᵃˡᵍ := x ^ d
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (ContinuousSMulDiscrete.isOpen_stabilizer (Γ Kᵥ) a) (one_mem _)
    let L : IntermediateField Kᵥ (Kᵥᵃˡᵍ) := IntermediateField.fixedField N.1.1
    have haL : a ∈ L := by
      intro g
      exact hN g.2
    let aL : L := ⟨a, haL⟩
    let B := IntegralClosure 𝒪ᵥ L
    let P := IsLocalRing.maximalIdeal B
    let H := P.inertia Gal(L/Kᵥ)
    let E : IntermediateField Kᵥ L := IntermediateField.fixedField H
    letI : FiniteDimensional Kᵥ L := by
      rw [← InfiniteGalois.isOpen_iff_finite]
      rw [InfiniteGalois.fixingSubgroup_fixedField
        (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup (Γ Kᵥ))]
      exact N.isOpen'
    letI : IsGalois Kᵥ L := by
      rw [← InfiniteGalois.normal_iff_isGalois]
      rw [InfiniteGalois.fixingSubgroup_fixedField
        (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup (Γ Kᵥ))]
      infer_instance
    have haE : aL ∈ E := by
      intro τ
      have hmap := map_localInertiaGroup_eq_finiteInertia (v := v) N
      have hτmap : τ.1 ∈ Subgroup.map (AlgEquiv.restrictNormalHom L)
          (localInertiaGroup v) := by
        rw [hmap]
        exact τ.2
      obtain ⟨ρ, hρ, hρτ⟩ := hτmap
      apply Subtype.ext
      change (algebraMap L (Kᵥᵃˡᵍ)) (τ.1 aL) =
        (algebraMap L (Kᵥᵃˡᵍ)) aL
      calc
        (algebraMap L (Kᵥᵃˡᵍ)) (τ.1 aL) =
            ρ ((algebraMap L (Kᵥᵃˡᵍ)) aL) := by
              rw [← hρτ]
              exact AlgEquiv.restrictNormal_commutes ρ L aL
        _ = (algebraMap L (Kᵥᵃˡᵍ)) aL := hx ⟨ρ, hρ⟩
    let aE : E := ⟨aL, haE⟩
    let D := IntegralClosure 𝒪ᵥ E
    let q := IsLocalRing.maximalIdeal D
    haveI : FiniteDimensional Kᵥ E := FiniteDimensional.left Kᵥ E L
    letI : IsInertiaField Kᵥ L P E := by
      dsimp only [E, H]
      exact {
        toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/Kᵥ) Kᵥ L
          (P.inertia Gal(L/Kᵥ)) }
    have he : q.ramificationIdx 𝒪ᵥ = 1 :=
      finiteInertiaField_ramificationIdx_eq_one (v := v) L E
    letI : IsFractionRing D E := by
      dsimp only [D]
      delta IntegralClosure
      exact integralClosure.isFractionRing_of_finite_extension Kᵥ E
    letI : Module.Finite 𝒪ᵥ D := by
      dsimp only [D]
      change Module.Finite 𝒪ᵥ (integralClosure 𝒪ᵥ E)
      exact IsIntegralClosure.finite 𝒪ᵥ Kᵥ E (integralClosure 𝒪ᵥ E)
    letI : IsDedekindDomain D := by
      dsimp only [D]
      change IsDedekindDomain (integralClosure 𝒪ᵥ E)
      exact IsIntegralClosure.isDedekindDomain 𝒪ᵥ Kᵥ E (integralClosure 𝒪ᵥ E)
    letI : Module.IsTorsionFree 𝒪ᵥ D := by
      rw [Module.isTorsionFree_iff_faithfulSMul]
      rw [faithfulSMul_iff_algebraMap_injective]
      intro r s hrs
      apply Subtype.ext
      apply (algebraMap Kᵥ E).injective
      have hrs' := congrArg Subtype.val hrs
      change (algebraMap Kᵥ E) (r : Kᵥ) = (algebraMap Kᵥ E) (s : Kᵥ) at hrs'
      exact hrs'
    letI : FaithfulSMul 𝒪ᵥ D := by
      exact Module.isTorsionFree_iff_faithfulSMul.mp
        (inferInstance : Module.IsTorsionFree 𝒪ᵥ D)
    let p := IsLocalRing.maximalIdeal 𝒪ᵥ
    have hp : p ≠ ⊥ := by
      dsimp only [p]
      exact IsDiscreteValuationRing.not_a_field 𝒪ᵥ
    have hfac := Ideal.map_algebraMap_eq_finsetProd_pow (R := D) hp
    have hmap : Ideal.map (algebraMap 𝒪ᵥ D) p = q := by
      dsimp only [q] at he ⊢
      simpa [IsLocalRing.primesOver_eq D hp, he] using hfac
    letI : q.LiesOver p := by dsimp only [q, p]; infer_instance
    have hq : q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp q
    letI : IsDiscreteValuationRing D := {
      not_a_field' := by simpa only [q] using hq }
    let piD : D := algebraMap 𝒪ᵥ D (tameUniformizer v)
    have hqspan : q = Ideal.span {piD} := by
      rw [← hmap]
      rw [show p = Ideal.span {tameUniformizer v} from
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
          K v (tameUniformizer_spec v)]
      rw [Ideal.map_span, Set.image_singleton]
    have hirr : Irreducible piD :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer piD).2 hqspan
    have haE0 : aE ≠ 0 := by
      intro h
      apply hx0
      apply eq_zero_of_pow_eq_zero
      simpa [a, aL, aE] using
        congrArg (fun z : E ↦ ((z.1 : L) : Kᵥᵃˡᵍ)) h
    obtain ⟨z, u, hdecomp⟩ :=
      IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hirr haE0
    let j : E →ₐ[𝒪ᵥ] (Kᵥᵃˡᵍ) :=
      (L.val.comp E.val).restrictScalars 𝒪ᵥ
    letI : Algebra D Aᵥ := (IntegralClosure.map j).toAlgebra
    letI : IsScalarTower 𝒪ᵥ D Aᵥ := IsScalarTower.of_algebraMap_eq' <| by
      ext r
      rfl
    letI : Algebra D (Kᵥᵃˡᵍ) :=
      (j.toRingHom.comp (algebraMap D E)).toAlgebra
    letI : IsScalarTower D E (Kᵥᵃˡᵍ) := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower D Aᵥ (Kᵥᵃˡᵍ) := IsScalarTower.of_algebraMap_eq' <| by
      ext r
      rfl
    have hdecompK : x ^ d =
        j (algebraMap D E (u : D)) *
          j ((algebraMap D E piD) ^ z) := by
      change j aE = j (u • (algebraMap D E piD) ^ z)
      exact congrArg j hdecomp
    have hpiK : j (algebraMap D E piD) =
        algebraMap 𝒪ᵥ (Kᵥᵃˡᵍ) (tameUniformizer v) := by
      rfl
    let uK : Kᵥᵃˡᵍ := j (algebraMap D E (u : D))
    let beta : Kᵥᵃˡᵍ :=
      (IsAlgClosed.exists_pow_nat_eq uK (tameDegree_pos v)).choose
    have hbeta : beta ^ d = uK := by
      dsimp only [beta, d]
      exact (IsAlgClosed.exists_pow_nat_eq uK (tameDegree_pos v)).choose_spec
    have huIntegral : IsIntegral 𝒪ᵥ uK := by
      dsimp only [uK]
      exact (u : D).2.map j
    let betaA : Aᵥ := ⟨beta, IsIntegral.of_pow (tameDegree_pos v) <| by
      rw [hbeta]
      exact huIntegral⟩
    have hbetaA : betaA ^ d = algebraMap D Aᵥ (u : D) := by
      apply Subtype.ext
      exact hbeta
    have hbetaUnit : IsUnit betaA :=
      (isUnit_pow_iff (tameDegree_pos v).ne').mp <| by
        rw [hbetaA]
        exact IsUnit.map (algebraMap D Aᵥ) u.isUnit
    have hEfixed (w : E) (τ : localInertiaGroup v) : τ.1 (j w) = j w := by
      have hτL : AlgEquiv.restrictNormalHom L τ.1 ∈ H := by
        have hmap := map_localInertiaGroup_eq_finiteInertia (v := v) N
        have hτmap : AlgEquiv.restrictNormalHom
            (IntermediateField.fixedField N.1.1) τ.1 ∈
            Subgroup.map
              (AlgEquiv.restrictNormalHom (IntermediateField.fixedField N.1.1))
              (localInertiaGroup v) := ⟨τ.1, τ.2, rfl⟩
        rw [hmap] at hτmap
        simpa only [L, H, P, B] using hτmap
      have hw := w.2 ⟨AlgEquiv.restrictNormalHom L τ.1, hτL⟩
      change (AlgEquiv.restrictNormalHom L τ.1) w.1 = w.1 at hw
      change τ.1 ((algebraMap L (Kᵥᵃˡᵍ)) ((algebraMap E L) w)) =
        (algebraMap L (Kᵥᵃˡᵍ)) ((algebraMap E L) w)
      calc
        τ.1 ((algebraMap L (Kᵥᵃˡᵍ)) ((algebraMap E L) w)) =
            (algebraMap L (Kᵥᵃˡᵍ))
              ((AlgEquiv.restrictNormalHom L τ.1) ((algebraMap E L) w)) :=
          (AlgEquiv.restrictNormal_commutes τ.1 L ((algebraMap E L) w)).symm
        _ = (algebraMap L (Kᵥᵃˡᵍ)) ((algebraMap E L) w) := by
          exact congrArg (algebraMap L (Kᵥᵃˡᵍ)) hw
    have hbetaPowFixed : ∀ τ : localInertiaGroup v,
        τ.1 • (betaA ^ d) = betaA ^ d := by
      intro τ
      rw [hbetaA]
      apply Subtype.ext
      change τ.1 (j (algebraMap D E (u : D))) =
        j (algebraMap D E (u : D))
      exact hEfixed (algebraMap D E (u : D)) τ
    have hbetaFixedA : σ.1 • betaA = betaA :=
      localInertia_fixes_of_isUnit_of_pow_fixed (v := v)
        hbetaUnit hbetaPowFixed σ
    have hbetaFixed : σ.1 beta = beta := by
      exact congrArg Subtype.val hbetaFixedA
    let alpha : Kᵥᵃˡᵍ := tameUniformizerRoot v
    have halpha : alpha ^ d =
        algebraMap 𝒪ᵥ (Kᵥᵃˡᵍ) (tameUniformizer v) := by
      exact (tameUniformizerRoot_spec v).trans
        (IsScalarTower.algebraMap_apply 𝒪ᵥ Kᵥ (Kᵥᵃˡᵍ) (tameUniformizer v)).symm
    have hdecompK' : x ^ d = uK * (alpha ^ d) ^ z := by
      calc
        x ^ d = j (algebraMap D E (u : D)) *
            j ((algebraMap D E piD) ^ z) := hdecompK
        _ = uK * (j (algebraMap D E piD)) ^ z := by
          rw [map_zpow₀]
        _ = uK * (alpha ^ d) ^ z := by rw [hpiK, halpha]
    have hbeta0 : beta ≠ 0 := by
      intro h
      apply hbetaUnit.ne_zero
      apply Subtype.ext
      exact h
    have halpha0 : alpha ≠ 0 := by
      exact tameUniformizerRoot_ne_zero v
    have hdenom0 : beta * alpha ^ z ≠ 0 :=
      mul_ne_zero hbeta0 (zpow_ne_zero z halpha0)
    have hdenomPow : (beta * alpha ^ z) ^ d = x ^ d := by
      rw [mul_pow, hbeta]
      have hz : (alpha ^ z) ^ d = (alpha ^ d) ^ z := by
        simpa only [zpow_natCast] using zpow_comm alpha z (d : ℤ)
      rw [hz, hdecompK']
    let gamma : Kᵥᵃˡᵍ := x / (beta * alpha ^ z)
    have hgammaPow : gamma ^ d = 1 := by
      dsimp only [gamma]
      rw [div_pow, hdenomPow, div_self]
      exact pow_ne_zero d hx0
    let gammaA : Aᵥ := ⟨gamma, IsIntegral.of_pow (tameDegree_pos v) <| by
      rw [hgammaPow]
      exact isIntegral_one⟩
    have hgammaPowA : gammaA ^ d = 1 := by
      apply Subtype.ext
      exact hgammaPow
    have hgammaUnit : IsUnit gammaA :=
      (isUnit_pow_iff (tameDegree_pos v).ne').mp <| by rw [hgammaPowA]; exact isUnit_one
    have hgammaPowFixed : ∀ τ : localInertiaGroup v,
        τ.1 • (gammaA ^ d) = gammaA ^ d := by
      intro τ
      rw [hgammaPowA]
      apply Subtype.ext
      exact map_one τ.1
    have hgammaFixedA : σ.1 • gammaA = gammaA :=
      localInertia_fixes_of_isUnit_of_pow_fixed (v := v)
        hgammaUnit hgammaPowFixed σ
    have hgammaFixed : σ.1 gamma = gamma :=
      congrArg Subtype.val hgammaFixedA
    have hxsplit : x = gamma * (beta * alpha ^ z) := by
      exact (div_mul_cancel₀ x hdenom0).symm
    calc
      σ.1 x = σ.1 (gamma * (beta * alpha ^ z)) := congrArg σ.1 hxsplit
      _ = σ.1 gamma * (σ.1 beta * σ.1 (alpha ^ z)) := by rw [map_mul, map_mul]
      _ = gamma * (beta * alpha ^ z) := by rw [hgammaFixed, hbetaFixed, map_zpow₀, hσα]
      _ = x := hxsplit.symm
