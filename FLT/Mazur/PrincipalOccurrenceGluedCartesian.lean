/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluedTransitions
public import FLT.Mazur.SchemeGlueDataMapCartesian

/-!
# Cartesian whole-chart squares of occurrence transitions

The cartesian common-union refinements imply that the already constructed
global transition pulls back each whole chart exactly.
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

/-- The typed overlap refinement square is cartesian. -/
theorem principalOccurrenceGluingOverlapMap_isPullback (i t : Shrink.{u} ι) :
    IsPullback (principalOccurrenceGluingOverlapMap e x y hxy i t)
      ((principalOccurrenceStageGlueData e y).f i t)
      ((principalOccurrenceStageGlueData e x).f i t)
      (principalOccurrenceGluingChartMap e x y hxy i) := by
  unfold principalOccurrenceGluingOverlapMap principalOccurrenceGluingChartMap
  exact principalOccurrenceCommonTransition_isPullback e x.val
    (principalOccurrenceGluingBijective e x) hxy (principalOccurrenceGluingBijective e y) _ _

/-- Refinement pulls back the image of each whole glued chart exactly. -/
theorem principalOccurrenceGluedTransition_preimage (i : Shrink.{u} ι) :
    principalOccurrenceGluedTransition e x y hxy ⁻¹'
        Set.range ((principalOccurrenceStageGlueData e x).ι i) =
      Set.range ((principalOccurrenceStageGlueData e y).ι i) := by
  let D := principalOccurrenceStageGlueData e x
  let E := principalOccurrenceStageGlueData e y
  let f := principalOccurrenceGluingChartMap e x y hxy
  let q := principalOccurrenceGluedTransition e x y hxy
  have hq := principalOccurrenceGluedTransition_chart e x y hxy
  change q ⁻¹' Set.range (D.ι i) = Set.range (E.ι i)
  ext z
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨j, w, rfl⟩ := E.ι_jointly_surjective z
    change Shrink.{u} ι at j
    have he : D.ι j (f j w) = D.ι i v := by
      rw [← Scheme.Hom.comp_apply, ← hq j]
      exact hv.symm
    obtain ⟨r, hr, _⟩ := (D.ι_eq_iff j i (f j w) v).mp he
    obtain ⟨s, _hs, hw⟩ := Scheme.exists_preimage_of_isPullback
      (principalOccurrenceGluingOverlapMap_isPullback e x y hxy j i) r w hr
    refine ⟨(E.t j i ≫ E.f i j) s, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, E.glue_condition j i]
    rw [Scheme.Hom.comp_apply, hw]
  · rintro ⟨w, rfl⟩
    exact ⟨f i w, (congrArg (fun k : E.U i ⟶ D.glued ↦ k w) (hq i)).symm⟩

/-- Every whole chart square of the global refinement is cartesian. -/
theorem principalOccurrenceGluedTransition_isPullback (i : Shrink.{u} ι) :
    IsPullback (principalOccurrenceGluingChartMap e x y hxy i)
      ((principalOccurrenceStageGlueData e y).ι i)
      ((principalOccurrenceStageGlueData e x).ι i)
      (principalOccurrenceGluedTransition e x y hxy) := by
  let _ := (principalOccurrenceStageGlueData e x).ι_isOpenImmersion i
  let _ := (principalOccurrenceStageGlueData e y).ι_isOpenImmersion i
  apply IsOpenImmersion.isPullback
  · exact principalOccurrenceGluedTransition_chart e x y hxy i
  · ext z
    exact Set.ext_iff.mp (principalOccurrenceGluedTransition_preimage e x y hxy i) z

end FLT.Mazur.FiniteTypeRelationModel
