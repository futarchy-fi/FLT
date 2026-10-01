/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicCharacter
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Residue action on local cyclotomic extensions

Transport the Eisenstein construction to arbitrary presentations of the prime
cyclotomic extension. Its integral closure has the base residue field, so every
Galois automorphism belongs to finite inertia.
-/

@[expose] public noncomputable section

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

open IsLocalRing

namespace LocalCyclotomic

variable (p : ℕ) [Fact p.Prime]
variable (E : Type*) [Field E] [Algebra ℚ_[p] E] [Algebra ℤ_[p] E]
  [IsScalarTower ℤ_[p] ℚ_[p] E] [IsCyclotomicExtension {p} ℚ_[p] E]
  [IsLocalRing (integralClosure ℤ_[p] E)]

/-- Every residue class in the cyclotomic integral closure comes from the base. -/
theorem integralClosure_residue_surjective :
    ∀ x : integralClosure ℤ_[p] E, ∃ r : ℤ_[p],
      residue _ (algebraMap ℤ_[p] (integralClosure ℤ_[p] E) r) = residue _ x := by
  obtain ⟨F, instF, instKF, instFinF, instRF, instTowerF, instCyclF,
    S, instS, instDomS, instDvrS, instRS, instFinS, instSF, instTowerS,
    instFracS, instClosS, _, _, hf⟩ := exists_totallyRamified_cyclotomic p
  have : FaithfulSMul ℤ_[p] S :=
    (faithfulSMul_iff_algebraMap_injective ℤ_[p] S).mpr <| by
      intro a b hab
      apply (IsFractionRing.injective ℤ_[p] ℚ_[p])
      apply (algebraMap ℚ_[p] F).injective
      simpa only [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap S F) hab
  let e : S ≃ₐ[ℤ_[p]] integralClosure ℤ_[p] E :=
    (IsIntegralClosure.equiv ℤ_[p] S F (integralClosure ℤ_[p] F)).trans
      ((IsCyclotomicExtension.algEquiv {p} ℚ_[p] F E).restrictScalars ℤ_[p]).mapIntegralClosure
  have hsur : Function.Surjective (algebraMap (ResidueField ℤ_[p]) (ResidueField S)) := by
    apply (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp ?_).2
    rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal ℤ_[p]) (maximalIdeal S)] at hf
    exact hf
  intro x
  obtain ⟨a, ha⟩ := hsur (residue S (e.symm x))
  obtain ⟨r, rfl⟩ := residue_surjective (R := ℤ_[p]) a
  refine ⟨r, ?_⟩
  have he := congrArg (ResidueField.mapEquiv e.toRingEquiv) ha
  change residue _ (e (algebraMap ℤ_[p] S r)) = residue _ (e (e.symm x)) at he
  simpa only [e.commutes, e.apply_symm_apply] using he

/-- Finite local cyclotomic automorphisms act trivially on the residue field. -/
theorem integralClosure_residue_fixed (σ : Gal(E/ℚ_[p]))
    (x : integralClosure ℤ_[p] E) :
    residue _ (((σ.restrictScalars ℤ_[p]).mapIntegralClosure) x) = residue _ x := by
  obtain ⟨r, hr⟩ := integralClosure_residue_surjective p E x
  let e := (σ.restrictScalars ℤ_[p]).mapIntegralClosure
  have he := congrArg (ResidueField.mapEquiv e.toRingEquiv) hr
  change residue _ (e (algebraMap ℤ_[p] (integralClosure ℤ_[p] E) r)) =
    residue _ (e x) at he
  rw [e.commutes] at he
  exact he.symm.trans hr

end LocalCyclotomic

namespace LocalCyclotomic

variable (p : ℕ) [Fact p.Prime]
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (rationalPlace p)
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (rationalPlace p)

set_option backward.isDefEq.respectTransparency.types false in
/-- The p-adic Eisenstein residue calculation in the completion presentation. -/
theorem completion_residue_surjective (L : Type*) [Field L] [Algebra Kv L]
    [Algebra O L] [IsScalarTower O Kv L] [IsCyclotomicExtension {p} Kv L]
    [IsLocalRing (integralClosure O L)] :
    ∀ x : integralClosure O L, ∃ r : O,
      residue _ (algebraMap O (integralClosure O L) r) = residue _ x := by
  let eK : ℚ_[p] ≃+* Kv := (Padic.adicCompletionEquiv (NumberField.RingOfIntegers ℚ)
    ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  let eR : ℤ_[p] ≃+* O := (PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ)
    ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  let : Algebra ℚ_[p] Kv := eK.toRingHom.toAlgebra
  let : Algebra ℚ_[p] L := ((algebraMap Kv L).comp eK.toRingHom).toAlgebra
  let : IsScalarTower ℚ_[p] Kv L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra ℤ_[p] L := ((algebraMap ℚ_[p] L).comp
    (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  let : IsScalarTower ℤ_[p] ℚ_[p] L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsCyclotomicExtension {1} ℚ_[p] Kv :=
    IsCyclotomicExtension.singleton_one_of_algebraMap_bijective eK.surjective
  have : IsCyclotomicExtension {p} ℚ_[p] L := by
    apply (IsCyclotomicExtension.iff_union_singleton_one {p} ℚ_[p] L).mpr
    simpa only [Set.union_comm] using
      (IsCyclotomicExtension.trans {1} {p} ℚ_[p] Kv L (algebraMap Kv L).injective)
  have hcomm : (algebraMap O L).comp eR.toRingHom = algebraMap ℤ_[p] L := by
    ext r
    change algebraMap O L (eR r) = algebraMap Kv L (eK (r : ℚ_[p]))
    rw [IsScalarTower.algebraMap_apply O Kv L]
    congr 1
    exact PadicInt.coe_adicCompletionIntegersEquiv_apply
      (NumberField.RingOfIntegers ℚ) ⟨p, Fact.out⟩ r
  let e : integralClosure ℤ_[p] L ≃+* integralClosure O L :=
    { toFun := fun x ↦ ⟨x.1, (eR.isIntegral_iff hcomm x.1).mp x.2⟩
      invFun := fun x ↦ ⟨x.1, (eR.isIntegral_iff hcomm x.1).mpr x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let : IsLocalRing (integralClosure ℤ_[p] L) :=
    IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  intro x
  obtain ⟨r, hr⟩ := integralClosure_residue_surjective p L (e.symm x)
  refine ⟨eR r, ?_⟩
  have he := congrArg (ResidueField.mapEquiv e) hr
  change residue _ (e (algebraMap ℤ_[p] (integralClosure ℤ_[p] L) r)) =
    residue _ (e (e.symm x)) at he
  rw [e.apply_symm_apply] at he
  convert he using 1
  congr 1
  apply Subtype.ext
  exact DFunLike.congr_fun hcomm r

set_option synthInstance.maxHeartbeats 100000 in
-- The integral-closure scalar towers require extra instance-search time.
/-- Every automorphism of a finite completion cyclotomic extension is in inertia. -/
theorem completion_inertia_eq_top
    (L : IntermediateField Kv (AlgebraicClosure Kv))
    [IsCyclotomicExtension {p} Kv L] :
    (maximalIdeal (IntegralClosure O L)).inertia Gal(L/Kv) = ⊤ := by
  let : IsLocalRing (integralClosure O L) :=
    inferInstanceAs (IsLocalRing (IntegralClosure O L))
  apply top_unique
  intro σ _
  change ∀ x : integralClosure O L, σ • x - x ∈ maximalIdeal _
  intro x
  obtain ⟨r, hr⟩ := completion_residue_surjective p L x
  let e := (σ.restrictScalars O).mapIntegralClosure
  have he := congrArg (ResidueField.mapEquiv e.toRingEquiv) hr
  change residue _ (e (algebraMap O (integralClosure O L) r)) = residue _ (e x) at he
  rw [e.commutes] at he
  apply (residue_eq_zero_iff _).mp
  rw [map_sub, sub_eq_zero]
  exact he.symm.trans hr

local notation "Ω" => AlgebraicClosure Kv

/-- A primitive root in the chosen local algebraic closure. -/
def completionZeta : Ω := (HasEnoughRootsOfUnity.exists_primitiveRoot Ω p).choose

lemma completionZeta_spec : IsPrimitiveRoot (completionZeta p) p :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot Ω p).choose_spec

/-- The finite cyclotomic subfield of the chosen algebraic closure. -/
def completionCyclotomicField : IntermediateField Kv Ω :=
  IntermediateField.adjoin Kv {completionZeta p}

instance completionCyclotomicField_isCyclotomicExtension :
    IsCyclotomicExtension {p} Kv (completionCyclotomicField p) :=
  (completionZeta_spec p).intermediateField_adjoin_isCyclotomicExtension Kv

instance completionCyclotomicField_finiteDimensional :
    FiniteDimensional Kv (completionCyclotomicField p) :=
  IsCyclotomicExtension.finiteDimensional {p} Kv _

instance completionCyclotomicField_isGalois : IsGalois Kv (completionCyclotomicField p) :=
  IsCyclotomicExtension.isGalois {p} Kv _

end LocalCyclotomic
