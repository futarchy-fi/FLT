/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ResidualCharacteristic
public import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Module.Compact

/-!
# Normalization of a three-adic order

The normalization of a finite free domain over `ℤ_[3]` is a complete discrete
valuation ring with finite residue field of characteristic three. Its topology
comes from the spectral norm extending the three-adic norm on the fraction field,
and agrees with the finite module topology.

Use `open scoped ThreeAdicPlan` to enable the canonical algebraic and topological
instances. `NormalizedOrderData` records these structures and the compatible,
continuous coefficient maps; `normalization_padic_order` constructs the package.
-/

@[expose] public section

noncomputable section

namespace ThreeAdicPlan

open scoped nonZeroDivisors

variable (R : Type*) [CommRing R] [Algebra ℤ_[3] R] [IsDomain R]
  [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]

/-- The induced three-adic field structure on the fraction field of an order. -/
scoped instance fractionAlgebra : Algebra ℚ_[3] (FractionRing R) :=
  (IsFractionRing.lift (K := ℚ_[3])
    (FaithfulSMul.algebraMap_injective ℤ_[3] (FractionRing R))).toAlgebra

scoped instance fractionScalarTower : IsScalarTower ℤ_[3] ℚ_[3] (FractionRing R) :=
  .of_algebraMap_eq fun x ↦
    (IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective ℤ_[3] (FractionRing R)) x).symm

/-- The fraction field of a finite free three-adic order is finite-dimensional. -/
scoped instance fractionFiniteDimensional : FiniteDimensional ℚ_[3] (FractionRing R) :=
  Module.Finite.of_isLocalization ℤ_[3] R ℤ_[3]⁰

/-- The normalization is the integral closure in the order's own fraction field. -/
abbrev NormalizedOrder := integralClosure ℤ_[3] (FractionRing R)

/-- The normalization is finite over the three-adic integers. -/
theorem normalizedOrder_finite : Module.Finite ℤ_[3] (NormalizedOrder R) :=
  IsIntegralClosure.finite ℤ_[3] ℚ_[3] (FractionRing R) (NormalizedOrder R)

/-- The normalization is free over the three-adic integers. -/
theorem normalizedOrder_free : Module.Free ℤ_[3] (NormalizedOrder R) :=
  IsIntegralClosure.module_free ℤ_[3] ℚ_[3] (FractionRing R) (NormalizedOrder R)

/-- Normalizing the order does not change its fraction field. -/
theorem normalizedOrder_isFractionRing : IsFractionRing (NormalizedOrder R) (FractionRing R) :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    ℤ_[3] ℚ_[3] (FractionRing R) (NormalizedOrder R)

/-- The normalization is a Dedekind domain. -/
theorem normalizedOrder_isDedekindDomain : IsDedekindDomain (NormalizedOrder R) :=
  IsIntegralClosure.isDedekindDomain ℤ_[3] ℚ_[3] (FractionRing R) (NormalizedOrder R)

/-- The integral rank agrees with the degree of the fraction field. -/
theorem normalizedOrder_finrank :
    Module.finrank ℤ_[3] (NormalizedOrder R) = Module.finrank ℚ_[3] (FractionRing R) :=
  IsIntegralClosure.rank ℤ_[3] ℚ_[3] (FractionRing R) (NormalizedOrder R)

/-- The natural embedding of the original order into its normalization. -/
def toNormalizedOrder : R →ₐ[ℤ_[3]] NormalizedOrder R :=
  (IsScalarTower.toAlgHom ℤ_[3] R (FractionRing R)).codRestrict _ fun r ↦
    (Algebra.IsIntegral.isIntegral (R := ℤ_[3]) r).map
      (IsScalarTower.toAlgHom ℤ_[3] R (FractionRing R))

omit [IsDomain R] [Module.Free ℤ_[3] R] in
@[simp]
theorem coe_toNormalizedOrder (r : R) :
    (toNormalizedOrder R r : FractionRing R) = algebraMap R (FractionRing R) r := rfl

omit [IsDomain R] [Module.Free ℤ_[3] R] in
/-- The normalization map is injective. -/
theorem toNormalizedOrder_injective : Function.Injective (toNormalizedOrder R) := by
  intro x y h
  exact IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)

/-- The spectral norm extending the three-adic norm. -/
scoped instance fractionNormedField : NontriviallyNormedField (FractionRing R) :=
  spectralNorm.nontriviallyNormedField ℚ_[3] (FractionRing R)

/-- The spectral norm respects scalar multiplication by the three-adic field. -/
scoped instance fractionNormedAlgebra : NormedAlgebra ℚ_[3] (FractionRing R) :=
  spectralNorm.normedAlgebra ℚ_[3] (FractionRing R)

/-- Integrality over the three-adic integers is exactly the closed unit ball condition. -/
theorem isIntegral_iff_norm_le_one (x : FractionRing R) :
    IsIntegral ℤ_[3] x ↔ ‖x‖ ≤ 1 := by
  change IsIntegral ℤ_[3] x ↔ spectralNorm ℚ_[3] (FractionRing R) x ≤ 1
  rw [spectralNorm, spectralValue_le_one_iff
    (minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[3]) x))]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[3] hx, Polynomial.coeff_map]
    exact ((minpoly ℤ_[3] x).coeff n).property
  · intro hx
    have hlift : minpoly ℚ_[3] x ∈ Polynomial.lifts (algebraMap ℤ_[3] ℚ_[3]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hx n⟩, rfl⟩
    obtain ⟨p, hp, _, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
      (minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[3]) x))
    refine ⟨p, hm, ?_⟩
    change Polynomial.aeval x p = 0
    rw [← Polynomial.aeval_map_algebraMap ℚ_[3], hp]
    exact minpoly.aeval ℚ_[3] x

/-- The normalization, viewed as a valuation subring of its fraction field. -/
def normalizedValuationSubring : ValuationSubring (FractionRing R) where
  toSubring := (integralClosure ℤ_[3] (FractionRing R)).toSubring
  mem_or_inv_mem' x := by
    change IsIntegral ℤ_[3] x ∨ IsIntegral ℤ_[3] x⁻¹
    simp only [isIntegral_iff_norm_le_one, norm_inv]
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · exact Or.inr (inv_le_one_of_one_le₀ h)

/-- The normalization is local. -/
theorem normalizedOrder_isLocalRing : IsLocalRing (NormalizedOrder R) :=
  inferInstanceAs (IsLocalRing (normalizedValuationSubring R))

attribute [scoped instance] normalizedOrder_finite normalizedOrder_free
  normalizedOrder_isFractionRing normalizedOrder_isDedekindDomain normalizedOrder_isLocalRing

/-- The normalization cannot be a field, since it is integral over `ℤ_[3]`. -/
theorem normalizedOrder_not_isField : ¬ IsField (NormalizedOrder R) := by
  intro h
  exact IsDiscreteValuationRing.not_isField ℤ_[3]
    (isField_of_isIntegral_of_isField
      (FaithfulSMul.algebraMap_injective ℤ_[3] (NormalizedOrder R)) h)

/-- The normalization is a discrete valuation ring. -/
theorem normalizedOrder_isDiscreteValuationRing : IsDiscreteValuationRing (NormalizedOrder R) :=
  ((IsDiscreteValuationRing.TFAE (NormalizedOrder R)
    (normalizedOrder_not_isField R)).out 3 1).mp
      (inferInstance : IsDedekindDomain (NormalizedOrder R))

/-- The normalization has a finite residue field. -/
theorem normalizedOrder_finite_residueField :
    Finite (IsLocalRing.ResidueField (NormalizedOrder R)) :=
  IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[3]) (S := NormalizedOrder R)
    (Finite.of_equiv (ZMod 3) (PadicInt.residueField).symm.toEquiv)

/-- The normalization's residue field has characteristic three. -/
theorem normalizedOrder_residueField_charP :
    CharP (IsLocalRing.ResidueField (NormalizedOrder R)) 3 := by
  have := normalizedOrder_finite_residueField R
  exact charP_three_of_finite_padic_algebra _

attribute [scoped instance] normalizedOrder_isDiscreteValuationRing
  normalizedOrder_finite_residueField normalizedOrder_residueField_charP

/-- The original order acts on its normalization through the canonical embedding. -/
scoped instance normalizedOrderAlgebra : Algebra R (NormalizedOrder R) :=
  (toNormalizedOrder R).toRingHom.toAlgebra

scoped instance normalizedOrderScalarTower : IsScalarTower ℤ_[3] R (NormalizedOrder R) :=
  .of_algebraMap_eq fun x ↦ ((toNormalizedOrder R).commutes x).symm

scoped instance normalizedOrderFractionScalarTower :
    IsScalarTower R (NormalizedOrder R) (FractionRing R) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The scalar action of the three-adic integers on the fraction field is continuous. -/
scoped instance fractionContinuousSMul : ContinuousSMul ℤ_[3] (FractionRing R) := by
  apply continuousSMul_of_algebraMap
  rw [IsScalarTower.algebraMap_eq ℤ_[3] ℚ_[3] (FractionRing R)]
  exact (continuous_algebraMap ℚ_[3] (FractionRing R)).comp continuous_subtype_val

/-- The normalization is compact in the topology inherited from its fraction field. -/
scoped instance normalizedOrderCompactSpace : CompactSpace (NormalizedOrder R) :=
  Module.Finite.compactSpace ℤ_[3] (NormalizedOrder R)

/-- The fraction field is complete for the extended three-adic norm. -/
theorem fraction_completeSpace : CompleteSpace (FractionRing R) :=
  FiniteDimensional.complete ℚ_[3] (FractionRing R)

/-- The normalization is complete in its induced uniform structure. -/
theorem normalizedOrder_completeSpace : CompleteSpace (NormalizedOrder R) := inferInstance

/-- The induced topology on the normalization is its finite module topology. -/
theorem normalizedOrder_isModuleTopology : IsModuleTopology ℤ_[3] (NormalizedOrder R) := by
  let b := Module.Free.chooseBasis ℤ_[3] (NormalizedOrder R)
  let e := b.equivFun.symm
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  exact IsModuleTopology.of_isQuotientMap _ e.toLinearMap
    (hc.isClosedMap.isQuotientMap hc e.surjective)

open scoped Pointwise in
/-- The normalization is complete for powers of its maximal ideal. -/
theorem normalizedOrder_isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (NormalizedOrder R)) (NormalizedOrder R) where
  prec' f hf := by
    let m := IsLocalRing.maximalIdeal (NormalizedOrder R)
    let S n : Set (NormalizedOrder R) := f n +ᵥ ((m ^ n : Ideal (NormalizedOrder R)) : Set _)
    have hS n : S (n + 1) ⊆ S n := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
      simpa [S] using (hf n.le_succ).symm
    have h n : IsClosed (S n) := (IsNoetherianRing.isClosed_ideal (m ^ n)).vadd (f n)
    obtain ⟨L, hL⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hS (by simp [S]) h
    refine ⟨L, fun n ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
    simpa [SModEq.sub_mem] using hy

attribute [scoped instance] fraction_completeSpace normalizedOrder_completeSpace
  normalizedOrder_isModuleTopology normalizedOrder_isAdicComplete

/-- The extended norm gives the standard finite-dimensional field topology. -/
theorem fraction_isModuleTopology : IsModuleTopology ℚ_[3] (FractionRing R) :=
  isModuleTopologyOfFiniteDimensional

attribute [scoped instance] fraction_isModuleTopology

variable [TopologicalSpace R] [IsModuleTopology ℤ_[3] R]

/-- The normalization map is continuous for the coefficient ring's module topology. -/
theorem continuous_toNormalizedOrder : Continuous (toNormalizedOrder R) :=
  IsModuleTopology.continuous_of_linearMap (toNormalizedOrder R).toLinearMap

/-- The original coefficient ring acts continuously on its normalization. -/
scoped instance normalizedOrderContinuousSMul : ContinuousSMul R (NormalizedOrder R) :=
  continuousSMul_of_algebraMap _ _ (continuous_toNormalizedOrder R)

/-- The original coefficient ring acts continuously on the fraction field. -/
scoped instance fractionOrderContinuousSMul : ContinuousSMul R (FractionRing R) := by
  apply continuousSMul_of_algebraMap
  rw [IsScalarTower.algebraMap_eq R (NormalizedOrder R) (FractionRing R)]
  exact continuous_subtype_val.comp (continuous_toNormalizedOrder R)

/-- Normalization data with the fixed models `K = FractionRing R` and
`O = integralClosure ℤ_[3] K`. The algebra and topology instances are the canonical
ones supplied in the `ThreeAdicPlan` scope, rather than additional choices. -/
structure NormalizedOrderData where
  /-- The integral coefficient embedding. -/
  coefficientMap : R →ₐ[ℤ_[3]] NormalizedOrder R
  /-- The embedding agrees with the original map into the fraction field. -/
  coefficientMap_eq : coefficientMap = toNormalizedOrder R
  /-- The induced map from the three-adic field. -/
  fractionMap : ℚ_[3] →ₐ[ℤ_[3]] FractionRing R
  /-- Compatibility with the canonical extension of the structure map. -/
  fractionMap_eq : fractionMap = IsScalarTower.toAlgHom ℤ_[3] ℚ_[3] (FractionRing R)
  /-- Finite degree of the fraction field. -/
  finiteDimensional : FiniteDimensional ℚ_[3] (FractionRing R)
  /-- The normalization has the same fraction field. -/
  isFractionRing : IsFractionRing (NormalizedOrder R) (FractionRing R)
  /-- The normalized order is a DVR. -/
  isDiscreteValuationRing : IsDiscreteValuationRing (NormalizedOrder R)
  /-- Completeness for the maximal ideal. -/
  isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (NormalizedOrder R)) (NormalizedOrder R)
  /-- Finiteness over the three-adic integers. -/
  finite : Module.Finite ℤ_[3] (NormalizedOrder R)
  /-- Freeness over the three-adic integers. -/
  free : Module.Free ℤ_[3] (NormalizedOrder R)
  /-- Finiteness of the residue field. -/
  finiteResidueField : Finite (IsLocalRing.ResidueField (NormalizedOrder R))
  /-- The residue characteristic. -/
  residueCharP : CharP (IsLocalRing.ResidueField (NormalizedOrder R)) 3
  /-- The standard topology on the integral model. -/
  orderModuleTopology : IsModuleTopology ℤ_[3] (NormalizedOrder R)
  /-- The standard topology on the generic fibre. -/
  fieldModuleTopology : IsModuleTopology ℚ_[3] (FractionRing R)
  /-- Completeness of the fraction field. -/
  fieldComplete : CompleteSpace (FractionRing R)
  /-- Completeness of the integral model in its induced uniformity. -/
  orderComplete : CompleteSpace (NormalizedOrder R)
  /-- Continuity of coefficient extension. -/
  continuous_coefficientMap : Continuous coefficientMap
  /-- Continuity of the three-adic field embedding. -/
  continuous_fractionMap : Continuous fractionMap
  /-- Continuity of the integral model's inclusion. -/
  continuous_orderMap : Continuous (algebraMap (NormalizedOrder R) (FractionRing R))
  /-- Continuous scalar extension from the original order. -/
  continuous_order_smul : ContinuousSMul R (NormalizedOrder R)
  /-- Continuous scalar extension to the generic fibre. -/
  continuous_fraction_smul : ContinuousSMul R (FractionRing R)
  /-- The normalized order acts continuously on the generic fibre. -/
  continuous_normalized_smul : ContinuousSMul (NormalizedOrder R) (FractionRing R)

-- All maps in the package are fixed by the compatibility fields, so the generated
-- constructor injectivity lemma reduces to a tautology under simplification.
attribute [nolint simpNF] NormalizedOrderData.mk.injEq

/-- A finite free three-adic domain admits the complete normalization package. -/
@[nolint unusedArguments]
theorem normalization_padic_order [IsTopologicalRing R] [IsLocalRing R] :
    Nonempty (NormalizedOrderData R) := by
  exact ⟨{
    coefficientMap := toNormalizedOrder R
    coefficientMap_eq := rfl
    fractionMap := IsScalarTower.toAlgHom ℤ_[3] ℚ_[3] (FractionRing R)
    fractionMap_eq := rfl
    finiteDimensional := inferInstance
    isFractionRing := inferInstance
    isDiscreteValuationRing := inferInstance
    isAdicComplete := inferInstance
    finite := inferInstance
    free := inferInstance
    finiteResidueField := inferInstance
    residueCharP := inferInstance
    orderModuleTopology := inferInstance
    fieldModuleTopology := inferInstance
    fieldComplete := inferInstance
    orderComplete := inferInstance
    continuous_coefficientMap := continuous_toNormalizedOrder R
    continuous_fractionMap := continuous_algebraMap ℚ_[3] (FractionRing R)
    continuous_orderMap := continuous_subtype_val
    continuous_order_smul := inferInstance
    continuous_fraction_smul := inferInstance
    continuous_normalized_smul := inferInstance }⟩

end ThreeAdicPlan
