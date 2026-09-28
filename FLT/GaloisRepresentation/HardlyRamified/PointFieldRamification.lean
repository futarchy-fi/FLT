/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.Unramified
public import FLT.GaloisRepresentation.HardlyRamified.CategoryDInertia

/-!
# Ramification in full point fields

Compare the order of the full local inertia action with the arithmetic
ramification index of the finite point field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open NumberField
namespace ThreeAdicPlan
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "Ov" => v.adicCompletionIntegers K

/-- Torsion-free modules over a Dedekind domain are flat. -/
theorem flatIntegralClosureHelper
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsDedekindDomain R] [Module.IsTorsionFree R M] : Module.Flat R M :=
  inferInstance

/-- In a finite local Galois extension, the ramification index is the order of inertia. -/
theorem localRamificationIdx_eq_card_inertia
    (C : IntermediateField Kv (AlgebraicClosure Kv))
    [FiniteDimensional Kv C] [IsGalois Kv C]
    : (IsLocalRing.maximalIdeal (IntegralClosure Ov C)).ramificationIdx Ov =
      Nat.card ((IsLocalRing.maximalIdeal (IntegralClosure Ov C)).inertia Gal(C/Kv)) := by
  let B := IntegralClosure Ov C
  let P := IsLocalRing.maximalIdeal B
  let p := IsLocalRing.maximalIdeal Ov
  let : IsFractionRing B C := by
    dsimp only [B]
    delta IntegralClosure
    exact integralClosure.isFractionRing_of_finite_extension Kv C
  let : Module.Finite Ov B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.finite Ov Kv C (integralClosure Ov C)
  let : Module.IsTorsionFree Ov B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap Kv C).injective
    exact congrArg Subtype.val hxy
  let : Module.Flat Ov B :=
    @flatIntegralClosureHelper Ov B _ _ Algebra.toModule _ (by exact this)
  let : IsDedekindDomain B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.isDedekindDomain Ov Kv C (integralClosure Ov C)
  let : P.LiesOver p := by dsimp only [P, p]; infer_instance
  let : SMulDistribClass Gal(C/Kv) B C := ⟨fun g b x ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  let : IsGaloisGroup Gal(C/Kv) Ov B :=
    IsGaloisGroup.of_isFractionRing Gal(C/Kv) Ov B Kv C
  let : Finite (Ov ⧸ p) := inferInstanceAs (Finite (IsLocalRing.ResidueField Ov))
  let : Finite p.ResidueField := inferInstance
  let : PerfectField p.ResidueField := inferInstance
  calc
    P.ramificationIdx Ov = p.ramificationIdxIn B :=
      (Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(C/Kv)).symm
    _ = Nat.card (P.inertia Gal(C/Kv)) := (Ideal.card_inertia_eq_ramificationIdxIn p P).symm


/-- The arithmetic ramification index at the induced global prime is the size of the
image of local absolute inertia in the global Galois group. -/
theorem inducedPrime_ramificationIdx_eq_card_localInertiaImage
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [Normal K L] :
    (NumberField.InertiaComparison.localInducedPrime v L).ramificationIdx (𝓞 K) =
      Nat.card ((localInertiaGroup v).map
        (NumberField.InertiaComparison.localRestriction v L)) := by
  let C := NumberField.InertiaComparison.localCompositum v L
  let I := localInertiaGroup v
  let f := (AlgEquiv.restrictNormalHom C).comp I.subtype
  let g := (NumberField.InertiaComparison.localRestriction v L).comp I.subtype
  have hker : f.ker = g.ker := by
    ext σ
    change σ.val ∈ (AlgEquiv.restrictNormalHom C).ker ↔
      σ.val ∈ (NumberField.InertiaComparison.localRestriction v L).ker
    rw [IntermediateField.restrictNormalHom_ker,
      NumberField.InertiaComparison.localCompositum_fixingSubgroup]
  have hcard : Nat.card f.range = Nat.card g.range := by
    calc
      Nat.card f.range = Nat.card (I ⧸ f.ker) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).symm.toEquiv
      _ = Nat.card (I ⧸ g.ker) := congrArg (fun H : Subgroup I ↦ Nat.card (I ⧸ H)) hker
      _ = Nat.card g.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have hf : f.range =
      (IsLocalRing.maximalIdeal (IntegralClosure Ov C)).inertia Gal(C/Kv) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact map_localInertiaGroup_eq_inertia v C
  have hg : g.range =
      I.map (NumberField.InertiaComparison.localRestriction v L) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨w, e, hw, he⟩ :=
    NumberField.InertiaComparison.exists_inducedPrime_completion_embedding v L
  rw [hw, NumberField.InertiaComparison.ramificationIdx_eq_of_completion_equiv v w C
    (NumberField.InertiaComparison.completionEquivLocalCompositum v L w e he),
    localRamificationIdx_eq_card_inertia, ← hf, hcard, hg]

/-- The integral action and restriction to its full point field have inertia images of
the same order. -/
theorem FiniteContinuousGaloisModule.inertiaTwo_card_eq (W : FiniteContinuousGaloisModule) :
    e_two W.integralGaloisRep = Nat.card ((localInertiaGroup twoAdicPlace).map
      (NumberField.InertiaComparison.localRestriction twoAdicPlace W.pointField)) := by
  let I := localInertiaGroup twoAdicPlace
  let f := inertiaTwoAction W.integralGaloisRep
  let g := (NumberField.InertiaComparison.localRestriction twoAdicPlace W.pointField).comp I.subtype
  have hker : f.ker = g.ker := by
    ext σ
    change f σ = 1 ↔ g σ = 1
    rw [← Units.val_inj]
    have he : (f σ : Module.End ℤ W) = W.integralGaloisRep
        (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ.val) := by
      change W.integralGaloisRep _ = W.integralGaloisRep _
      congr 4
      exact Subsingleton.elim _ _
    have hg : g σ = AlgEquiv.restrictNormalHom W.pointField
        (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ.val) := by
      change AlgEquiv.restrictNormalHom W.pointField _ =
        AlgEquiv.restrictNormalHom W.pointField _
      congr 4
      exact Subsingleton.elim _ _
    rw [he, hg, Units.val_one]
    rw [← MonoidHom.mem_ker (f := AlgEquiv.restrictNormalHom W.pointField),
      IntermediateField.restrictNormalHom_ker,
      W.pointField_fixingSubgroup, W.mem_pointActionKernel]
    exact LinearMap.ext_iff
  have hcard : Nat.card f.range = Nat.card g.range := by
    calc
      Nat.card f.range = Nat.card (I ⧸ f.ker) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).symm.toEquiv
      _ = Nat.card (I ⧸ g.ker) := congrArg (fun H : Subgroup I ↦ Nat.card (I ⧸ H)) hker
      _ = Nat.card g.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  change Nat.card f.range = _
  rw [hcard, MonoidHom.range_comp, Subgroup.range_subtype]

/-- At the induced prime of the full point field, the arithmetic ramification index is
the image-order invariant `e_two` of the full integral point representation. -/
theorem FiniteContinuousGaloisModule.pointField_ramificationIdx_at_two
    (W : FiniteContinuousGaloisModule) :
    (NumberField.InertiaComparison.localInducedPrime twoAdicPlace W.pointField).ramificationIdx
      (𝓞 ℚ) = e_two W.integralGaloisRep := by
  rw [inducedPrime_ramificationIdx_eq_card_localInertiaImage, W.inertiaTwo_card_eq]

/-- Every prime above two in the full point field has ramification index `e_two`.
The field is Galois, so the index is independent of the chosen prime. -/
theorem FiniteContinuousGaloisModule.pointField_allPrimes_ramificationIdx_at_two
    (W : FiniteContinuousGaloisModule) (P : Ideal (𝓞 W.pointField)) [P.IsPrime]
    [P.LiesOver twoAdicPlace.asIdeal] :
    P.ramificationIdx (𝓞 ℚ) = e_two W.integralGaloisRep := by
  let L := W.pointField
  let : SMulDistribClass Gal(L/ℚ) (𝓞 L) L := ⟨fun g b x ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  let : IsGaloisGroup Gal(L/ℚ) (𝓞 ℚ) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ) (𝓞 ℚ) (𝓞 L) ℚ L
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx twoAdicPlace.asIdeal P Gal(L/ℚ),
    Ideal.ramificationIdxIn_eq_ramificationIdx twoAdicPlace.asIdeal
      (NumberField.InertiaComparison.localInducedPrime twoAdicPlace W.pointField) Gal(L/ℚ)]
  exact W.pointField_ramificationIdx_at_two

end ThreeAdicPlan
