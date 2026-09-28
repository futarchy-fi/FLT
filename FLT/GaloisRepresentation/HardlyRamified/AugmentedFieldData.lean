/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedField
public import FLT.GaloisRepresentation.HardlyRamified.FiniteFlatUnramified

/-!
# Arithmetic data of the augmented point field

The full field of points of the product with the Kummer object contains `K₀`,
is finite Galois and totally complex, is unramified outside two and three, and
has ramification index dividing three at every prime above two.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ThreeAdicPlan

/-- Unramifiedness of the full point action implies arithmetic unramifiedness
of its point field at every prime outside the exceptional set. -/
theorem FiniteContinuousGaloisModule.pointField_isUnramifiedIn
    (W : FiniteContinuousGaloisModule) {S : Finset ℕ} (h : UnramifiedOutside S W)
    (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) :
    Algebra.IsUnramifiedIn (NumberField.RingOfIntegers W.pointField)
      hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
  apply NumberField.InertiaComparison.isUnramifiedIn_of_localInertia_le_ker
  intro σ hσ
  rw [MonoidHom.mem_ker, NumberField.InertiaComparison.localRestriction, MonoidHom.comp_apply]
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
    W.pointField_fixingSubgroup, W.mem_pointActionKernel]
  intro w
  convert h.inertia_trivial p hp hpS σ hσ w using 1
  congr 4
  exact Subsingleton.elim _ _

/-- The augmented point field of a simple category-D object is unramified outside
of the primes two and three. -/
theorem augmentedField_isUnramifiedIn {H : FiniteFlatObject ZInvTwo} (hs : Simple H)
    (hD : InCategoryD H) (p : ℕ) (hp : p.Prime) (hpS : p ∉ ({2, 3} : Finset ℕ)) :
    Algebra.IsUnramifiedIn (NumberField.RingOfIntegers (AugmentedField H))
      hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
  (augmentedObject H).points.pointField_isUnramifiedIn
    ((augmentedObject H).unramifiedOutside_of_killedBy_three
      (augmentedObject_killedBy_three hs hD)) p hp hpS

/-- The augmented full point field contains the sextic Kummer field, is Galois and
totally complex, is unramified away from two and three, and has ramification index
dividing three at every prime above two. -/
theorem augmented_field_data (H : FiniteFlatObject ZInvTwo) (hs : Simple H)
    (hD : InCategoryD H) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      IsPointField (H.prod kummerTwoObject) L ∧ Nonempty (K₀ →ₐ[ℚ] L) ∧
      IsGalois ℚ L ∧ NumberField.IsTotallyComplex L ∧
      (∀ (p : ℕ) (hp : p.Prime), p ∉ ({2, 3} : Finset ℕ) →
        Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L)
          hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ∧
      ∀ (P : Ideal (NumberField.RingOfIntegers L))
        [P.IsPrime] [P.LiesOver twoAdicPlace.asIdeal],
        P.ramificationIdx (NumberField.RingOfIntegers ℚ) ∣ 3 := by
  refine ⟨(augmentedObject H).points.pointField, augmentedField_isPointField H,
    ⟨kummerTwoFieldToAugmentedField H⟩, inferInstance, inferInstance, ?_, ?_⟩
  · exact augmentedField_isUnramifiedIn hs hD
  · exact augmentedField_ramificationIdx_dvd_three hs hD

end ThreeAdicPlan
