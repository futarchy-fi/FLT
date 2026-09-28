/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryDInertia
public import FLT.GaloisRepresentation.HardlyRamified.CategoryDSimple
public import FLT.GaloisRepresentation.HardlyRamified.KummerObjectField
public import FLT.GaloisRepresentation.HardlyRamified.PointFieldRamification
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The augmented point field

Adjoining the Kummer object's full point action to that of an object `H`
produces a finite Galois, totally complex field containing `K₀`. For simple
objects of category D, the augmented action is killed by three and its
inertia image at two has order dividing three.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Augment a model by the explicit Kummer object for two. -/
def augmentedObject (H : FiniteFlatObject ZInvTwo) : FiniteFlatObject ZInvTwo :=
  H.prod kummerTwoObject

/-- The field cut out by the full action on the augmented point group. -/
abbrev AugmentedField (H : FiniteFlatObject ZInvTwo) : Type := PointField (augmentedObject H)

/-- The canonical augmented field realizes the full product point action. -/
theorem augmentedField_isPointField (H : FiniteFlatObject ZInvTwo) :
    IsPointField (H.prod kummerTwoObject) (AugmentedField H) := isPointField_self _

/-- The augmented field contains the original object's point field. -/
def pointFieldToAugmentedField (H : FiniteFlatObject ZInvTwo) :
    PointField H →ₐ[ℚ] AugmentedField H :=
  IntermediateField.inclusion (H.points.pointField_le_prod_left kummerTwoPoints)

/-- The augmented field contains the sextic Kummer field through the second factor. -/
def kummerTwoFieldToAugmentedField (H : FiniteFlatObject ZInvTwo) : K₀ →ₐ[ℚ] AugmentedField H :=
  (IntermediateField.inclusion (H.points.pointField_le_prod_right kummerTwoPoints)).comp
    kummerTwoPointFieldEquiv.symm.toAlgHom

instance kummerTwoField_isTotallyComplex : NumberField.IsTotallyComplex K₀ where
  isComplex v := by
    apply NumberField.InfinitePlace.not_isReal_iff_isComplex.mp
    intro hv
    let φ := NumberField.InfinitePlace.embedding_of_isReal hv
    obtain ⟨b, hb⟩ := exists_integral_sqrt_neg_three
    have he := congrArg (fun b : NumberField.RingOfIntegers K₀ ↦ φ (b : K₀)) hb
    have he' : (φ (b : K₀)) ^ 2 = -3 := by simpa [map_ofNat] using he
    nlinarith [sq_nonneg (φ (b : K₀))]

instance (H : FiniteFlatObject ZInvTwo) : NumberField.IsTotallyComplex (AugmentedField H) := by
  let : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
  exact NumberField.isTotallyComplex_of_algebra K₀ (AugmentedField H)

/-- Augmentation preserves category D. -/
theorem augmentedObject_inCategoryD {H : FiniteFlatObject ZInvTwo} (hD : InCategoryD H) :
    InCategoryD (augmentedObject H) := hD.prod kummerTwoObject_inCategoryD

/-- Augmenting a simple category-D object still gives an object killed by three. -/
theorem augmentedObject_killedBy_three {H : FiniteFlatObject ZInvTwo} (hs : Simple H)
    (hD : InCategoryD H) : KilledBy 3 (augmentedObject H) :=
  (simple_D_killed_three H hs hD).prod kummerTwoObject_killedBy_three

/-- The full inertia image at two on the augmented object has order dividing three. -/
theorem augmentedField_inertiaTwo_order_dvd_three {H : FiniteFlatObject ZInvTwo} (hs : Simple H)
    (hD : InCategoryD H) : e_two (augmentedObject H).points.integralGaloisRep ∣ 3 :=
  (augmentedObject_inCategoryD hD).inertiaTwo_order_dvd_three
    (augmentedObject_killedBy_three hs hD)

/-- Every prime above two in the augmented point field has ramification index dividing three. -/
theorem augmentedField_ramificationIdx_dvd_three {H : FiniteFlatObject ZInvTwo} (hs : Simple H)
    (hD : InCategoryD H) (P : Ideal (NumberField.RingOfIntegers (AugmentedField H)))
    [P.IsPrime] [P.LiesOver twoAdicPlace.asIdeal] :
    P.ramificationIdx (NumberField.RingOfIntegers ℚ) ∣ 3 := by
  rw [(augmentedObject H).points.pointField_allPrimes_ramificationIdx_at_two P]
  exact augmentedField_inertiaTwo_order_dvd_three hs hD

/-- The field-theoretic and ramification-at-two data for the explicit augmented point field.
Unramifiedness outside two and three is a separate finite-flat-to-étale input. -/
theorem augmentedField_basicData (H : FiniteFlatObject ZInvTwo) (hs : Simple H)
    (hD : InCategoryD H) :
    IsPointField (H.prod kummerTwoObject) (AugmentedField H) ∧
      Nonempty (K₀ →ₐ[ℚ] AugmentedField H) ∧ IsGalois ℚ (AugmentedField H) ∧
      NumberField.IsTotallyComplex (AugmentedField H) ∧
      ∀ (P : Ideal (NumberField.RingOfIntegers (AugmentedField H)))
        [P.IsPrime] [P.LiesOver twoAdicPlace.asIdeal],
        P.ramificationIdx (NumberField.RingOfIntegers ℚ) ∣ 3 :=
  ⟨augmentedField_isPointField H, ⟨kummerTwoFieldToAugmentedField H⟩, inferInstance,
    inferInstance, augmentedField_ramificationIdx_dvd_three hs hD⟩

end ThreeAdicPlan
