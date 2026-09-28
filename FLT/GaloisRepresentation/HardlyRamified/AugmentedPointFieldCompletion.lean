/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedLocalModel
public import FLT.NumberField.Completion.FieldEquiv

/-!
# The three-adic completion as the local full point field

The embedding used for local restriction selects a prime above three. At that
prime the completion of the global point field is isomorphic, over `ℚ_[3]`, to
the full local point field of the actual base-changed finite flat model.
-/

@[expose] public noncomputable section

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

open NumberField

namespace ThreeAdicPlan

/-- The rational place above three in the presentation used by `Padic.adicCompletionEquiv`. -/
def threeAdicPointFieldPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨3, Nat.prime_three⟩

/-- The rational completion at three is the three-adic field. -/
def threeAdicPointFieldBaseEquiv : threeAdicPointFieldPlace.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[3] :=
  (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨3, Nat.prime_three⟩).symm.toAlgEquiv

/-- The completion at the prime selected by local restriction realizes the local full
point field, and the isomorphism extends the specified global embedding. -/
theorem FiniteFlatObject.exists_completion_equiv_localPointField
    (H : FiniteFlatObject ZInvTwo) :
    ∃ w : threeAdicPointFieldPlace.Extension (𝓞 (PointField H)),
      letI := completionAlgebraOfEquiv threeAdicPointFieldPlace threeAdicPointFieldBaseEquiv w
      ∃ e : w.1.adicCompletion (PointField H) ≃ₐ[ℚ_[3]] LocalPointField H.localFFAtThree,
        ∀ x : PointField H, (e (algebraMap (PointField H) _ x) : AlgebraicClosure ℚ_[3]) =
          H.points.pointFieldEmbedding ℚ_[3] x := by
  obtain ⟨w, g, hg, hrange⟩ := exists_adicCompletion_embedding_of_equiv
    threeAdicPointFieldPlace threeAdicPointFieldBaseEquiv
    (H.points.pointFieldEmbedding ℚ_[3])
  let := completionAlgebraOfEquiv threeAdicPointFieldPlace threeAdicPointFieldBaseEquiv w
  let e := g.equivFieldRange.trans
    (IntermediateField.equivOfEq (hrange.trans H.localPointField_eq_adjoin.symm))
  exact ⟨w, e, hg⟩

/-- The augmented global field has a completion which is the full point field of a
finite flat three-adic model killed by three. -/
theorem augmentedField_exists_completion_equiv_localPointField
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    KilledBy 3 (augmentedObject H).localFFAtThree ∧
      ∃ w : threeAdicPointFieldPlace.Extension (𝓞 (AugmentedField H)),
        letI := completionAlgebraOfEquiv threeAdicPointFieldPlace threeAdicPointFieldBaseEquiv w
        Nonempty (w.1.adicCompletion (AugmentedField H) ≃ₐ[ℚ_[3]]
          LocalPointField (augmentedObject H).localFFAtThree) := by
  refine ⟨augmentedObject_localFFAtThree_killedBy_three hs hD, ?_⟩
  obtain ⟨w, e, _⟩ := (augmentedObject H).exists_completion_equiv_localPointField
  exact ⟨w, ⟨e⟩⟩

end ThreeAdicPlan
