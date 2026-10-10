/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluedClosed

/-!
# Open chart images in the occurrence stages

Named chart opens retain the literal embeddings and their exact inverse
images along every geometric refinement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Small.{u} ι]

/-- The open image of a literal finite-stage chart. -/
def principalOccurrenceGluedChartOpen (x : PrincipalOccurrenceGluingStage e)
    (i : Shrink.{u} ι) : (principalOccurrenceStageGlueData e x).glued.Opens := by
  let _ := (principalOccurrenceStageGlueData e x).ι_isOpenImmersion i
  exact ((principalOccurrenceStageGlueData e x).ι i).opensRange

/-- The named chart open has exactly the underlying image of the literal embedding. -/
theorem principalOccurrenceGluedChartOpen_coe (x : PrincipalOccurrenceGluingStage e)
    (i : Shrink.{u} ι) :
    (principalOccurrenceGluedChartOpen e x i : Set (principalOccurrenceStageGlueData e x).glued) =
      Set.range ((principalOccurrenceStageGlueData e x).ι i) := rfl

/-- Every named chart open is affine. -/
theorem principalOccurrenceGluedChartOpen_isAffine (x : PrincipalOccurrenceGluingStage e)
    (i : Shrink.{u} ι) : IsAffineOpen (principalOccurrenceGluedChartOpen e x i) := by
  let _ := (principalOccurrenceStageGlueData e x).ι_isOpenImmersion i
  let _ : IsAffine ((principalOccurrenceStageGlueData e x).U i) :=
    inferInstanceAs (IsAffine (Spec (.of (Stage R (A ((equivShrink.{u} ι).symm i))
      (x.val.source ((equivShrink.{u} ι).symm i))))))
  exact isAffineOpen_opensRange ((principalOccurrenceStageGlueData e x).ι i)

/-- Refinement recovers each whole chart open by exact inverse image. -/
theorem principalOccurrenceGluedChartOpen_preimage (x y : PrincipalOccurrenceGluingStage e)
    (hxy : x ≤ y) (i : Shrink.{u} ι) :
    principalOccurrenceGluedTransition e x y hxy ⁻¹ᵁ principalOccurrenceGluedChartOpen e x i =
      principalOccurrenceGluedChartOpen e y i :=
  TopologicalSpace.Opens.ext (principalOccurrenceGluedTransition_preimage e x y hxy i)

end FLT.Mazur.FiniteTypeRelationModel
