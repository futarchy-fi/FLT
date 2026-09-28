/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalCoefficientConjugacy
public import FLT.GroupScheme.LocalInertiaPolynomial
public import FLT.GroupScheme.FontainePolynomialObstruction

/-!
# Fontaine obstructions over an unramified coefficient ring

Coefficient embeddings into a normal field are conjugate, so forbidden values
of a relative polynomial exclude arbitrary field embeddings. A relative power
basis then produces the quotient homomorphism required by Fontaine's property.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L E : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L] [IsGalois ℚ_[3] L]
  [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]
  {C : Type} [CommRing C] [Algebra ℤ_[3] C]
  [Algebra C (ThreeAdicIntegers L)] [IsScalarTower ℤ_[3] C (ThreeAdicIntegers L)]
  [FaithfulSMul C (ThreeAdicIntegers L)]
  [Algebra C (ThreeAdicIntegers E)] [IsScalarTower ℤ_[3] C (ThreeAdicIntegers E)]
  [FaithfulSMul C (ThreeAdicIntegers E)]

/-- A relative polynomial's forbidden value excludes embeddings into an
extension of no larger degree, even when the embeddings move the coefficients. -/
theorem threeAdicRelativeNoEmbeddingOfExcludedValue (pc : PowerBasis ℤ_[3] C)
    (P : Polynomial C) (n : ℕ)
    (hexcluded : ∀ x : ThreeAdicIntegers L,
      IsDiscreteValuationRing.addVal (ThreeAdicIntegers L) (Polynomial.aeval x P) ≠ (n : ℕ∞))
    (hdeg : Module.finrank ℚ_[3] E ≤ Module.finrank ℚ_[3] L)
    (y : ThreeAdicIntegers E)
    (hy : IsDiscreteValuationRing.addVal (ThreeAdicIntegers E) (Polynomial.aeval y P) =
      (n : ℕ∞)) : ¬ Nonempty (L →ₐ[ℚ_[3]] E) := by
  rintro ⟨i⟩
  have hdim : Module.finrank ℚ_[3] L = Module.finrank ℚ_[3] E :=
    le_antisymm
      (LinearMap.finrank_le_finrank_of_injective (f := i.toLinearMap) i.injective) hdeg
  have hsurj : Function.Surjective i :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := i.toLinearMap)).mp i.injective
  let e := AlgEquiv.ofBijective i ⟨i.injective, hsurj⟩
  let eInt : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers E :=
    (e.restrictScalars ℤ_[3]).mapIntegralClosure
  let f := IsScalarTower.toAlgHom ℤ_[3] C (ThreeAdicIntegers L)
  let g := eInt.symm.toAlgHom.comp (IsScalarTower.toAlgHom ℤ_[3] C (ThreeAdicIntegers E))
  obtain ⟨σ, hσ⟩ := threeAdicCoefficientEmbeddingsConjugate L pc f g
    (FaithfulSMul.algebraMap_injective C _) (eInt.symm.injective.comp
      (FaithfulSMul.algebraMap_injective C _))
  let j : ThreeAdicIntegers E ≃ₐ[C] ThreeAdicIntegers L :=
    { (eInt.symm.trans σ.symm).toRingEquiv with
      commutes' := fun c => by
        have h := congrArg (fun f : C →ₐ[ℤ_[3]] ThreeAdicIntegers L => f c) hσ
        change σ.symm (eInt.symm (algebraMap C (ThreeAdicIntegers E) c)) = _
        change σ (algebraMap C (ThreeAdicIntegers L) c) =
          eInt.symm (algebraMap C (ThreeAdicIntegers E) c) at h
        rw [← h, σ.symm_apply_apply] }
  apply hexcluded (j y)
  rw [Polynomial.aeval_algHom_apply]
  exact (IsDiscreteValuationRing.addValRingEquiv j.toRingEquiv _).trans hy

omit [IsGalois ℚ_[3] L] [FaithfulSMul C (ThreeAdicIntegers L)]
  [FaithfulSMul C (ThreeAdicIntegers E)] in
/-- A relative approximate root in a field with no embedding contradicts
Fontaine's property after restricting the coefficient scalars. -/
theorem notFontainePropertyOfRelativeApproximateRoot
    (pb : PowerBasis C (ThreeAdicIntegers L)) (m : ℚ) (y : ThreeAdicIntegers E)
    (hy : Polynomial.aeval y (minpoly C pb.gen) ∈ threeAdicValuationIdeal E m)
    (hLE : ¬ Nonempty (L →ₐ[ℚ_[3]] E)) :
    ¬ FontaineProperty (ThreeAdicIntegers L) m := by
  intro h
  obtain ⟨f⟩ := (pb.nonempty_algHom_quotient_iff (threeAdicValuationIdeal E m)).mpr ⟨y, hy⟩
  exact hLE ((fontaineProperty_integers_iff L m).mp h E ⟨f.restrictScalars ℤ_[3]⟩)

end ThreeAdicPlan
