/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluedTransitions

/-!
# Original chart projections into the glued occurrence stages

The finite gluing relations and the cartesian occurrence projections give
compatible maps from all original charts, natural under refinement.
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

variable [Small.{u} ι] (x : PrincipalOccurrenceGluingStage e)

set_option quotPrecheck false in
local notation "I" => (equivShrink ι).symm
local notation "D" => principalOccurrenceStageGlueData e x
local notation "H" => principalOccurrenceGluingBijective e x

/-- Both embeddings of a literal common occurrence agree in the glued stage. -/
theorem principalOccurrenceGluedCommon_incidence (i t : Shrink.{u} ι)
    (p : PrincipalOccurrenceCommon dst (I i) (I t)) :
    principalOccurrenceCommonLeft e x.val H (I i) (I t) p ≫ (D).ι i =
      principalOccurrenceCommonLeft e x.val H (I t) (I i)
        (principalOccurrenceCommonSwap dst (I i) (I t) p) ≫ (D).ι t := by
  let a := openImageUnionMap (principalOccurrenceCommonLeft e x.val H (I i) (I t)) p
  have ha : a ≫ (D).f i t = principalOccurrenceCommonLeft e x.val H (I i) (I t) p :=
    openImageUnionMap_fac (principalOccurrenceCommonLeft e x.val H (I i) (I t)) p
  have ht : a ≫ (D).t i t =
      openImageUnionMap (principalOccurrenceCommonLeft e x.val H (I t) (I i))
        (principalOccurrenceCommonSwap dst (I i) (I t) p) :=
    principalOccurrenceCommonUnionIso_fac e x.val H (principalOccurrenceGluingEquations e x)
      (I i) (I t) p
  calc
    _ = a ≫ (D).f i t ≫ (D).ι i := by
      erw [← Category.assoc, ha]
      rfl
    _ = a ≫ (D).t i t ≫ (D).f t i ≫ (D).ι t :=
      congrArg (fun k ↦ a ≫ k) ((D).glue_condition i t).symm
    _ = _ := by
      erw [← Category.assoc a, ht, ← Category.assoc]
      exact congrArg (fun k ↦ k ≫ (D).ι t)
        (openImageUnionMap_fac (principalOccurrenceCommonLeft e x.val H (I t) (I i))
        (principalOccurrenceCommonSwap dst (I i) (I t) p))

/-- The original affine chart maps into each glued stage via its ambient projection. -/
@[irreducible] def principalOccurrenceOriginalGluedChart (i : Shrink.{u} ι) :
    Spec (.of (A (I i))) ⟶ (D).glued :=
  principalOccurrenceAmbientProjection e x.val (I i) ≫ (D).ι i

/-- Original chart projections agree on every original literal common occurrence. -/
theorem principalOccurrenceOriginalGluedChart_incidence (i t : Shrink.{u} ι)
    (p : PrincipalOccurrenceCommon dst (I i) (I t)) :
    principalOccurrenceOriginalCommonLeft e (I i) (I t) p ≫
        principalOccurrenceOriginalGluedChart e x i =
      principalOccurrenceOriginalCommonLeft e (I t) (I i)
        (principalOccurrenceCommonSwap dst (I i) (I t) p) ≫
          principalOccurrenceOriginalGluedChart e x t := by
  unfold principalOccurrenceOriginalGluedChart
  have hi := principalOccurrenceOpenAt_recovery_assoc e x.val H
    (I i) p.2.1.val p.2.1.property ((D).ι i)
  have ht := principalOccurrenceOpenAt_recovery_assoc e x.val H
    (I t) p.2.2.val p.2.2.property ((D).ι t)
  exact hi.symm.trans ((congrArg
    (fun k ↦ principalOccurrenceOverlapProjection e x.val p.1 ≫ k)
    (principalOccurrenceGluedCommon_incidence e x i t p)).trans ht)

/-- The original chart maps commute with every global transition. -/
@[reassoc] theorem principalOccurrenceOriginalGluedChart_transition
    (y : PrincipalOccurrenceGluingStage e) (hxy : x ≤ y) (i : Shrink.{u} ι) :
    principalOccurrenceOriginalGluedChart e y i ≫ principalOccurrenceGluedTransition e x y hxy =
      principalOccurrenceOriginalGluedChart e x i := by
  unfold principalOccurrenceOriginalGluedChart
  erw [Category.assoc, principalOccurrenceGluedTransition_chart, ← Category.assoc]
  unfold principalOccurrenceGluingChartMap
  erw [principalOccurrenceAmbientProjection_transition]
  rfl

end FLT.Mazur.FiniteTypeRelationModel
