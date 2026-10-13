/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationInvariantRestriction
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Full envelope construction on an invariant source open

An invariant source open whose whole envelope lies in the original relation
produces an isomorphism from the FULL two-endpoint restriction to that envelope.
The construction retains the original relation arrow, not only its points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationRestriction
universe u
set_option backward.isDefEq.respectTransparency false
variable {P X Y : Scheme.{u}} (p q : P ⟶ X) (j : P ⟶ Y) [IsOpenImmersion j]
  (π : Y ⟶ X) (hj : j ≫ π = q) (U : X.Opens)

/-- The entire double restriction maps into the original envelope by its unchanged arrow. -/
def invariantEnvelopeMap : doubleDomain p q U.ι ⟶ Y := arrow p q U.ι ≫ j

instance invariantEnvelopeMap_isOpenImmersion :
    IsOpenImmersion (invariantEnvelopeMap p q j U) := by
  dsimp only [invariantEnvelopeMap, arrow]
  infer_instance

include hj in
omit [IsOpenImmersion j] in
/-- The full double restriction lands over its original restricted source. -/
theorem invariantEnvelopeMap_range_le :
    Set.range (invariantEnvelopeMap p q j U) ⊆ (π ⁻¹ᵁ U : Set Y) := by
  rintro _ ⟨z, rfl⟩
  change (invariantEnvelopeMap p q j U ≫ π) z ∈ U
  rw [invariantEnvelopeMap, Category.assoc, hj, arrow_snd]
  exact (snd p q U.ι z).property

include hj in
/-- Invariance and full envelope support lift both endpoints of every envelope point. -/
theorem invariantEnvelopeMap_range
    (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (hY : π ⁻¹ᵁ U ≤ j.opensRange) :
    Set.range (invariantEnvelopeMap p q j U) = (π ⁻¹ᵁ U : Set Y) := by
  apply Set.Subset.antisymm (invariantEnvelopeMap_range_le p q j π hj U)
  intro y hy
  obtain ⟨z, hz⟩ := hY hy
  have hq : q z ∈ U := by
    rw [← hj]
    change π (j z) ∈ U
    rwa [hz]
  have hp : p z ∈ U := by
    change z ∈ p ⁻¹ᵁ U
    rw [hU]
    exact hq
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback p U.ι) z ⟨p z, hp⟩ rfl
  have hwq : (pullback.fst p U.ι ≫ q) w = U.ι ⟨q z, hq⟩ := congrArg q hw
  obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (pullback.fst p U.ι ≫ q) U.ι) w ⟨q z, hq⟩ hwq
  refine ⟨v, ?_⟩
  change j (pullback.fst p U.ι (pullback.fst (pullback.fst p U.ι ≫ q) U.ι v)) = y
  rw [hv, hw, hz]

/-- The full two-endpoint relation is the actual envelope over the invariant source open. -/
def invariantEnvelopeIso
    (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (hY : π ⁻¹ᵁ U ≤ j.opensRange) :
    doubleDomain p q U.ι ≅ (π ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.isoOfRangeEq (invariantEnvelopeMap p q j U) (π ⁻¹ᵁ U).ι (by
    rw [invariantEnvelopeMap_range p q j π hj U hU hY, Scheme.Opens.range_ι])

/-- The isomorphism retains the unchanged original arrow into the envelope. -/
@[reassoc]
theorem invariantEnvelopeIso_hom_ι
    (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (hY : π ⁻¹ᵁ U ≤ j.opensRange) :
    (invariantEnvelopeIso p q j π hj U hU hY).hom ≫ (π ⁻¹ᵁ U).ι =
      arrow p q U.ι ≫ j :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse supplies the full restricted relation, preserving its original envelope map. -/
@[reassoc]
theorem invariantEnvelopeIso_inv_arrow
    (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (hY : π ⁻¹ᵁ U ≤ j.opensRange) :
    (invariantEnvelopeIso p q j π hj U hU hY).inv ≫ arrow p q U.ι ≫ j =
      (π ⁻¹ᵁ U).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

end FLT.Mazur.SchemeRelationRestriction
