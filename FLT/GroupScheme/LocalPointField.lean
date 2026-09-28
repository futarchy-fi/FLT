/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudExtension
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Point fields and the normalized different

The point field is the fixed field of the kernel of the action on geometric
points. Finiteness and continuity of the action make it a finite Galois extension.
For a finite extension of the three-adic field, the ring of integers is its
integral closure over `ℤ_[3]`. The normalized different exponent is the
multiplicity of its maximal ideal in the different, divided by its multiplicity
in `(3)`. This file does not assert Fontaine's ramification bound.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- The kernel of the Galois action on the geometric points of a model. -/
def FF.pointActionKernel (M : FF R K) :
    Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
  (MulAction.toPermHom (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) M.Points).ker

/-- Kernel membership means fixing every geometric point. -/
@[simp] theorem FF.mem_pointActionKernel (M : FF R K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    σ ∈ M.pointActionKernel ↔ ∀ x : M.Points, σ • x = x := by
  change MulAction.toPermHom _ M.Points σ = 1 ↔ _
  exact Equiv.ext_iff

/-- The kernel of the point action is normal. -/
instance pointActionKernelNormal (M : FF R K) : M.pointActionKernel.Normal := MonoidHom.normal_ker _

/-- A finite continuous action has open kernel. -/
theorem FF.pointActionKernel_isOpen (M : FF R K) :
    IsOpen (M.pointActionKernel : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) := by
  have he : (M.pointActionKernel : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) =
      ⋂ x : M.Points, {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K | σ • x = x} := by
    ext σ
    simp
  rw [he]
  exact isOpen_iInter_of_finite fun x ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ x x

/-- The field cut out by the Galois action on all geometric points. -/
def LocalPointField (M : FF R K) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField M.pointActionKernel

/-- The subgroup fixing the point field is exactly the action kernel. -/
theorem FF.localPointField_fixingSubgroup [PerfectField K] (M : FF R K) :
    (LocalPointField M).fixingSubgroup = M.pointActionKernel :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨M.pointActionKernel, M.pointActionKernel.isClosed_of_isOpen M.pointActionKernel_isOpen⟩

/-- The point field has finite degree. -/
instance localPointFieldFinite [PerfectField K] (M : FF R K) :
    FiniteDimensional K (LocalPointField M) := by
  apply (InfiniteGalois.isOpen_iff_finite (LocalPointField M)).mp
  rw [M.localPointField_fixingSubgroup]
  exact M.pointActionKernel_isOpen

/-- The point field is Galois over the generic base field. -/
instance localPointFieldGalois [PerfectField K] (M : FF R K) : IsGalois K (LocalPointField M) := by
  apply (InfiniteGalois.normal_iff_isGalois (LocalPointField M)).mp
  rw [M.localPointField_fixingSubgroup]
  infer_instance

/-- Every geometric coordinate value lies in the point field. -/
theorem FF.pointValue_mem_localPointField (M : FF R K)
    (f : K ⊗[R] M.CoordinateRing →ₐ[K] AlgebraicClosure K)
    (a : K ⊗[R] M.CoordinateRing) : f a ∈ LocalPointField M := by
  rw [LocalPointField, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have h := (M.mem_pointActionKernel σ).mp hσ (M.points (Additive.ofMul f))
  rw [← map_smul] at h
  have hf := M.points_bijective.1 h
  exact congrArg (fun q : Additive (K ⊗[R] M.CoordinateRing →ₐ[K] AlgebraicClosure K) =>
    q.toMul a) hf

section ThreeAdic

variable (L : Type*) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- The ring of integers of a finite three-adic extension, as an integral closure. -/
abbrev ThreeAdicIntegers := integralClosure ℤ_[3] L

/-- The ring of integers is finite over the three-adic integers. -/
instance threeAdicIntegersFinite : Module.Finite ℤ_[3] (ThreeAdicIntegers L) :=
  IsIntegralClosure.finite ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L)

/-- The ring of integers is free over the three-adic integers. -/
instance threeAdicIntegersFree : Module.Free ℤ_[3] (ThreeAdicIntegers L) := by
  have : Module.IsTorsionFree ℤ_[3] L := .trans_faithfulSMul ℤ_[3] ℚ_[3] L
  exact IsIntegralClosure.module_free ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L)

/-- The integral closure has the original extension as fraction field. -/
instance threeAdicIntegersFractionRing : IsFractionRing (ThreeAdicIntegers L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L)

/-- The integral closure in a finite three-adic extension is Dedekind. -/
instance threeAdicIntegersDedekind : IsDedekindDomain (ThreeAdicIntegers L) :=
  IsIntegralClosure.isDedekindDomain ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L)

/-- Integrality over `ℤ_[3]` is the closed unit ball condition for the spectral norm. -/
theorem isIntegral_iff_spectralNorm_le_one (x : L) :
    IsIntegral ℤ_[3] x ↔ spectralNorm ℚ_[3] L x ≤ 1 := by
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

/-- The integral closure in a finite three-adic extension is a valuation subring. -/
def threeAdicValuationSubring : ValuationSubring L where
  toSubring := (integralClosure ℤ_[3] L).toSubring
  mem_or_inv_mem' x := by
    let := spectralNorm.nontriviallyNormedField ℚ_[3] L
    change IsIntegral ℤ_[3] x ∨ IsIntegral ℤ_[3] x⁻¹
    simp only [isIntegral_iff_spectralNorm_le_one]
    change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
    rw [norm_inv]
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · exact Or.inr (inv_le_one_of_one_le₀ h)

/-- The valuation-subring description makes the ring of integers local. -/
instance threeAdicIntegersLocal : IsLocalRing (ThreeAdicIntegers L) :=
  inferInstanceAs (IsLocalRing (threeAdicValuationSubring L))

/-- The integral closure remains a nonfield because it is integral over `ℤ_[3]`. -/
theorem threeAdicIntegers_not_isField : ¬ IsField (ThreeAdicIntegers L) := by
  intro h
  have : Module.IsTorsionFree ℤ_[3] L := .trans_faithfulSMul ℤ_[3] ℚ_[3] L
  have : FaithfulSMul ℤ_[3] (ThreeAdicIntegers L) := inferInstance
  exact IsDiscreteValuationRing.not_isField ℤ_[3]
    (isField_of_isIntegral_of_isField
      (FaithfulSMul.algebraMap_injective ℤ_[3] (ThreeAdicIntegers L)) h)

/-- The ring of integers of a finite three-adic extension is a DVR. -/
instance threeAdicIntegersDVR : IsDiscreteValuationRing (ThreeAdicIntegers L) :=
  ((IsDiscreteValuationRing.TFAE (ThreeAdicIntegers L)
    (threeAdicIntegers_not_isField L)).out 3 1).mp
      (inferInstance : IsDedekindDomain (ThreeAdicIntegers L))

/-- The exponent of the maximal ideal in a nonzero integral ideal.
As with `normalizedFactors`, the value at the zero ideal is defined to be zero. -/
def threeAdicIdealOrder (I : Ideal (ThreeAdicIntegers L)) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors I).count
    (IsLocalRing.maximalIdeal (ThreeAdicIntegers L))

/-- The ideal valuation divided by the valuation of `(3)`, so that `v(3) = 1`. -/
def normalizedIdealOrder (I : Ideal (ThreeAdicIntegers L)) : ℚ :=
  (threeAdicIdealOrder L I : ℚ) / threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)})

/-- The valuation of the different ideal, normalized by `v(3) = 1`. -/
def normalizedDifferentExponent : ℚ :=
  normalizedIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L))

/-- The denominator in the normalized valuation is strictly positive. -/
theorem threeAdicIdealOrder_three_pos :
    0 < threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) := by
  classical
  have : IsLocalHom (algebraMap ℤ_[3] (ThreeAdicIntegers L)) :=
    (show (algebraMap ℤ_[3] (ThreeAdicIntegers L)).IsIntegral from
      fun x ↦ Algebra.IsIntegral.isIntegral x).isLocalHom
        (FaithfulSMul.algebraMap_injective ℤ_[3] (ThreeAdicIntegers L))
  have h3 : (3 : ThreeAdicIntegers L) ∈ IsLocalRing.maximalIdeal (ThreeAdicIntegers L) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    have hu : IsUnit (algebraMap ℤ_[3] (ThreeAdicIntegers L) 3) := by simpa only [map_ofNat] using h
    exact PadicInt.p_nonunit (IsLocalHom.map_nonunit _ hu)
  rw [threeAdicIdealOrder, Multiset.count_pos, Ideal.mem_normalizedFactors_iff]
  · exact ⟨inferInstance, Ideal.span_le.mpr (by simpa using h3)⟩
  · have : CharZero (ThreeAdicIntegers L) := Algebra.charZero_of_charZero ℤ_[3] _
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num

/-- The normalization assigns value one to the ideal `(3)`. -/
@[simp] theorem normalizedIdealOrder_three :
    normalizedIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) = 1 := by
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (threeAdicIdealOrder_three_pos L)))

/-- Ideal order scales by the exponent under taking powers. -/
@[simp] theorem threeAdicIdealOrder_pow (I : Ideal (ThreeAdicIntegers L)) (n : ℕ) :
    threeAdicIdealOrder L (I ^ n) = n * threeAdicIdealOrder L I := by
  classical
  simp only [threeAdicIdealOrder, UniqueFactorizationMonoid.normalizedFactors_pow,
    Multiset.count_nsmul]

/-- The different is nonzero, so the zero-ideal convention in ideal order is irrelevant here. -/
theorem threeAdicDifferent_ne_bot : differentIdeal ℤ_[3] (ThreeAdicIntegers L) ≠ ⊥ :=
  differentIdeal_ne_bot

/-- The normalized different exponent is nonnegative. -/
theorem normalizedDifferentExponent_nonneg : 0 ≤ normalizedDifferentExponent L := by
  unfold normalizedDifferentExponent normalizedIdealOrder
  positivity

end ThreeAdic
end ThreeAdicPlan
