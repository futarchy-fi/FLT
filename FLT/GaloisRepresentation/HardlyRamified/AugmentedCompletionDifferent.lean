/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedPointFieldCompletion
public import FLT.GroupScheme.FontaineDifferentHypothesis
public import FLT.GroupScheme.LocalDifferentEquiv

/-!
# The local different bound for an augmented-field completion

Transport the normalized different through the completion/point-field
isomorphism. This does not identify the completed different with the global
different ideal; that local-global comparison is a separate assertion.
-/

@[expose] public noncomputable section

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

open NumberField

namespace ThreeAdicPlan

/-- The actual normalized different of a completion above three, with the completed
rational base identified with `ℚ_[3]`. This is not the global prime-ideal exponent. -/
def pointFieldCompletionNormalizedDifferent (H : FiniteFlatObject ZInvTwo)
    (w : threeAdicPointFieldPlace.Extension (𝓞 (PointField H))) : ℚ := by
  let := completionAlgebraOfEquiv threeAdicPointFieldPlace threeAdicPointFieldBaseEquiv w
  let : Algebra ℤ_[3] (w.1.adicCompletion (PointField H)) :=
    Algebra.compHom _ (algebraMap ℤ_[3] ℚ_[3])
  let : IsScalarTower ℤ_[3] ℚ_[3] (w.1.adicCompletion (PointField H)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let := completion_finiteDimensional_of_equiv
    threeAdicPointFieldPlace threeAdicPointFieldBaseEquiv w
  exact normalizedDifferentExponent (w.1.adicCompletion (PointField H))

/-- Every completion above three has the normalized different of the local full point field. -/
theorem FiniteFlatObject.completion_normalizedDifferent_eq
    (H : FiniteFlatObject ZInvTwo)
    (w : threeAdicPointFieldPlace.Extension (𝓞 (PointField H))) :
    pointFieldCompletionNormalizedDifferent H w =
      normalizedDifferentExponent (LocalPointField H.localFFAtThree) := by
  obtain ⟨e⟩ := H.nonempty_completion_equiv_localPointField w
  let := completionAlgebraOfEquiv threeAdicPointFieldPlace threeAdicPointFieldBaseEquiv w
  let : Algebra ℤ_[3] (w.1.adicCompletion (PointField H)) :=
    Algebra.compHom _ (algebraMap ℤ_[3] ℚ_[3])
  let : IsScalarTower ℤ_[3] ℚ_[3] (w.1.adicCompletion (PointField H)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let := completion_finiteDimensional_of_equiv
    threeAdicPointFieldPlace threeAdicPointFieldBaseEquiv w
  exact normalizedDifferentExponent_eq_of_algEquiv e

/-- Fontaine's stated local hypothesis bounds the completed different at every prime
above three in the augmented field. -/
theorem augmentedField_completion_normalizedDifferent_lt
    (hF : FontaineDifferentBoundKilledThree)
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (w : threeAdicPointFieldPlace.Extension (𝓞 (AugmentedField H))) :
    pointFieldCompletionNormalizedDifferent (augmentedObject H) w < (3 / 2 : ℚ) := by
  rw [(augmentedObject H).completion_normalizedDifferent_eq w]
  exact hF _ (augmentedObject_localFFAtThree_killedBy_three hs hD)

/-- At the prime selected by local restriction, the completed and local point-field
different exponents agree. -/
theorem FiniteFlatObject.exists_completion_normalizedDifferent_eq
    (H : FiniteFlatObject ZInvTwo) :
    ∃ w : threeAdicPointFieldPlace.Extension (𝓞 (PointField H)),
      pointFieldCompletionNormalizedDifferent H w =
        normalizedDifferentExponent (LocalPointField H.localFFAtThree) := by
  obtain ⟨w, _, _⟩ := H.exists_completion_equiv_localPointField
  exact ⟨w, H.completion_normalizedDifferent_eq w⟩

/-- Fontaine's stated local hypothesis bounds the actual different of an augmented-field
completion, with no global different comparison assumed. -/
theorem augmentedField_exists_completion_normalizedDifferent_lt
    (hF : FontaineDifferentBoundKilledThree)
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    ∃ w : threeAdicPointFieldPlace.Extension (𝓞 (AugmentedField H)),
      pointFieldCompletionNormalizedDifferent (augmentedObject H) w < (3 / 2 : ℚ) := by
  obtain ⟨w, hw⟩ := (augmentedObject H).exists_completion_normalizedDifferent_eq
  exact ⟨w, hw ▸ hF _ (augmentedObject_localFFAtThree_killedBy_three hs hD)⟩

end ThreeAdicPlan
