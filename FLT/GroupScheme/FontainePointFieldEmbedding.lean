/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontainePointLifts
public import FLT.GroupScheme.FontaineRootCriterion
public import FLT.GroupScheme.LocalPointFieldPoints

/-!
# From compatible lifts of all points to Fontaine's field property

An injection from the integral points over the full point field to those over
an extension realizes every geometric point over that extension: both embed
in the same finite set, and the full point field realizes the whole set.
Galois correspondence then gives a field embedding.

At precision `m > 3/2`, compatible lifts losing one unit of precision give
such an injection. Consequently compatible lifting implies Fontaine's
property for the full ring of integers, not merely the coordinate algebra.
Existence of compatible lifts for arbitrary finite flat models and the
ramification-theoretic different estimate remain separate obligations.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable (M : FF ℤ_[3] ℚ_[3])
variable (E : Type) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

omit [FiniteDimensional ℚ_[3] E] in
/-- An injection of the full set of point-field integral points into the
integral points over an extension forces that extension to realize every
geometric point. No Galois equivariance of the injection is assumed. -/
theorem FF.geometricIntegralPoint_surjective_of_embedding
    (j : E →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3])
    (lift : (M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers (LocalPointField M)) ↪
      (M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E)) :
    Function.Surjective (M.geometricIntegralPoint E j) := by
  let e := M.localPointFieldIntegralPointsEquiv
  have hi := (M.geometricIntegralPoint_injective E j).comp
    (lift.injective.comp e.symm.injective)
  have hs := Finite.surjective_of_injective hi
  intro f
  obtain ⟨g, hg⟩ := hs f
  exact ⟨lift (e.symm g), hg⟩

/-- Merely embedding the full set of integral points suffices to embed the
full point field into the target extension. -/
theorem FF.nonempty_localPointField_algHom_of_pointEmbedding
    (lift : (M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers (LocalPointField M)) ↪
      (M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E)) :
    Nonempty (LocalPointField M →ₐ[ℚ_[3]] E) := by
  let j : E →ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3] := IsAlgClosed.lift
  exact M.nonempty_localPointField_algHom_of_integralPoints E j
    (M.geometricIntegralPoint_surjective_of_embedding E j lift)

/-- Simultaneously lifting all point-field integral points with loss of one
unit of precision yields an embedding of the full point field. -/
theorem FF.nonempty_localPointField_algHom_of_compatibleLifts (hM : KilledBy 3 M)
    {m : ℚ} (hm : 3 / 2 < m)
    (f : ThreeAdicIntegers (LocalPointField M) →ₐ[ℤ_[3]]
      ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m)
    (hlift : ∀ u : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers (LocalPointField M),
      ∃ v : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E,
        (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E (m - 1))).comp v =
          ((Ideal.Quotient.factorₐ ℤ_[3]
            (threeAdicValuationIdeal_antitone E (show m - 1 ≤ m by linarith))).comp f).comp u) :
    Nonempty (LocalPointField M →ₐ[ℚ_[3]] E) := by
  obtain ⟨lift⟩ := M.nonempty_integralPoint_embedding_of_lifts (LocalPointField M) E hM hm f hlift
  exact M.nonempty_localPointField_algHom_of_pointEmbedding E lift

/-- Compatible lifting at Fontaine precision implies the embedding property
for the full integers of the full point field. The lifting premise applies
to all approximate model points, and is not asserted here. -/
theorem FF.fontaineProperty_localPointField_of_compatibleLifting (hM : KilledBy 3 M)
    {m : ℚ} (hm : 3 / 2 < m)
    (hlift : ∀ (E : Type) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
      [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]
      (u : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m),
      ∃ v : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E,
        (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E (m - 1))).comp v =
          (Ideal.Quotient.factorₐ ℤ_[3]
            (threeAdicValuationIdeal_antitone E (show m - 1 ≤ m by linarith))).comp u) :
    FontaineProperty (ThreeAdicIntegers (LocalPointField M)) m := by
  rw [fontaineProperty_integers_iff]
  intro E _ _ _ _ _ ⟨f⟩
  apply M.nonempty_localPointField_algHom_of_compatibleLifts E hM hm f
  intro u
  exact hlift E (f.comp u)

end ThreeAdicPlan
