/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluingStage
public import FLT.Mazur.PrincipalOccurrenceCommonNaturality
public import FLT.Mazur.PrincipalOccurrenceCommonTransitionLaws

/-!
# Chart and overlap maps for the gluable-stage subtype

Typed wrappers retain the exact glue-data chart indices. Separate
compatibility lemmas keep the global constructor small for kernel checking.
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
  (x y : PrincipalOccurrenceGluingStage e) (hxy : x ≤ y)

/-- The ambient refinement, typed on the actual gluing charts. -/
@[irreducible] def principalOccurrenceGluingChartMap (i : Shrink.{u} ι) :
    (principalOccurrenceStageGlueData e y).U i ⟶ (principalOccurrenceStageGlueData e x).U i :=
  principalOccurrenceAmbientTransition hxy ((equivShrink ι).symm i)

/-- The full common-union refinement, typed on the actual gluing overlaps. -/
@[irreducible] def principalOccurrenceGluingOverlapMap (i t : Shrink.{u} ι) :
    (principalOccurrenceStageGlueData e y).V (i, t) ⟶
      (principalOccurrenceStageGlueData e x).V (i, t) :=
  principalOccurrenceCommonTransition e x.val (principalOccurrenceGluingBijective e x)
    hxy (principalOccurrenceGluingBijective e y) ((equivShrink ι).symm i)
    ((equivShrink ι).symm t)

/-- The overlap map retains the complete chart refinement square. -/
theorem principalOccurrenceGluingOverlapMap_fac (i t : Shrink.{u} ι) :
    principalOccurrenceGluingOverlapMap e x y hxy i t ≫
        (principalOccurrenceStageGlueData e x).f i t =
      (principalOccurrenceStageGlueData e y).f i t ≫
        principalOccurrenceGluingChartMap e x y hxy i := by
  unfold principalOccurrenceGluingOverlapMap principalOccurrenceGluingChartMap
  exact principalOccurrenceCommonTransition_fac e x.val
    (principalOccurrenceGluingBijective e x) hxy (principalOccurrenceGluingBijective e y) _ _

/-- The overlap map commutes with the full comparison isomorphism. -/
theorem principalOccurrenceGluingOverlapMap_comparison (i t : Shrink.{u} ι) :
    principalOccurrenceGluingOverlapMap e x y hxy i t ≫
        (principalOccurrenceStageGlueData e x).t i t =
      (principalOccurrenceStageGlueData e y).t i t ≫
        principalOccurrenceGluingOverlapMap e x y hxy t i := by
  unfold principalOccurrenceGluingOverlapMap
  exact principalOccurrenceCommonTransition_comparison e x.val
    (principalOccurrenceGluingBijective e x) hxy (principalOccurrenceGluingBijective e y)
    (principalOccurrenceGluingEquations e x) (principalOccurrenceGluingEquations e y) _ _

/-- The typed reflexive chart transition is the identity. -/
theorem principalOccurrenceGluingChartMap_id (i : Shrink.{u} ι) :
    principalOccurrenceGluingChartMap e x x le_rfl i = 𝟙 _ := by
  unfold principalOccurrenceGluingChartMap
  exact principalOccurrenceAmbientTransition_id e x.val _

/-- Typed chart transitions compose with their literal common index. -/
@[reassoc] theorem principalOccurrenceGluingChartMap_comp
    (z : PrincipalOccurrenceGluingStage e) (hyz : y ≤ z) (i : Shrink.{u} ι) :
    principalOccurrenceGluingChartMap e y z hyz i ≫
        principalOccurrenceGluingChartMap e x y hxy i =
      principalOccurrenceGluingChartMap e x z (hxy.trans hyz) i := by
  unfold principalOccurrenceGluingChartMap
  exact principalOccurrenceAmbientTransition_comp e x.val hxy hyz _

end FLT.Mazur.FiniteTypeRelationModel
