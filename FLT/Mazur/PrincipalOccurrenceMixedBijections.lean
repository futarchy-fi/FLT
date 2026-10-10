/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceRecoveredRestrictions
public import FLT.Mazur.PrincipalOccurrenceDiagramRefinement
public import FLT.Mazur.PrincipalFanMixedRestrictionPaths

/-!
# Cofinal bijections from surjective occurrence coordinates

Finite restrictions and simultaneous diagram refinement supply the full
ambient paths needed for kernel patching. All target labels remain shared.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalFanInitialRestrictionEquiv
  principalFanOriginalRestriction principalQuotientEquiv principalFanRestrictionProjection
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient
  FiniteRelationIterated.transition FiniteRelationLocalization.transition

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  [Finite ι] [∀ i, Finite (J i)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Finite κ]

/-- Recovered mixed-source restrictions give cofinal bijective refinements. -/
theorem exists_principalOccurrence_bijective_of_mixed_restrictions
    {x y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)}
    (hxy : x ≤ y) (hx : ∀ i k, Function.Surjective (x.hom i k))
    (ρ : ∀ i k l,
      PrincipalStage R (B (dst i k)) (b (dst i k)) (x.target (dst i k)) →ₐ[R]
        PrincipalFanRestrictionTarget (principalOccurrenceFan y i) k l)
    (hρ : ∀ i k l, (ρ i k l).comp (principalFanAmbient (principalOccurrenceFan x i) k) =
      (principalFanRestrictionInclusion (principalOccurrenceFan y i) k l).comp
        ((principalTransition (b (dst i l)) (principalOccurrence_target_mono hxy (dst i l))).comp
          (principalFanAmbient (principalOccurrenceFan x i) l)))
    (hrec : ∀ i k l,
      (principalFanRestrictionProjection (e i) (principalOccurrenceFan y i) k l).comp (ρ i k l) =
      (principalFanOriginalRestriction (e i) (principalOccurrenceFan y i) k l).comp
        (principalStageMap R (B (dst i k)) (b (dst i k)) (x.target (dst i k))))
    (bs : ∀ i, Finset (relationIdeal R (A i)))
    (bt : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ w : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      y ≤ w ∧ bs ≤ w.source ∧ bt ≤ w.target ∧
        ∀ i k, Function.Bijective (w.hom i k) := by
  obtain ⟨z, hyz, hbs, hbt, σ, hOld⟩ :=
    exists_principalOccurrence_diagram_refinement e y x.target ρ
      (principalOccurrence_target_mono hxy) hrec bs bt
  have hz := principalOccurrence_surjective_mono (hxy.trans hyz) hx
  have hpath (i : ι) (k l : J i) :
      ((σ i k l).comp (principalTransition (b (dst i k))
        (principalOccurrence_target_mono hyz (dst i k)))).comp
          (principalFanAmbient (principalOccurrenceFan y i) k) =
      (principalFanOldRestrictionInclusion (principalOccurrenceFan_mono hyz i) k l).comp
        ((principalTransition (b (dst i l))
          (principalOccurrence_target_mono hyz (dst i l))).comp
            (principalFanAmbient (principalOccurrenceFan y i) l)) := by
    apply principalFanMixedRestriction_path (e i)
      (principalOccurrenceFan_mono hxy i) (principalOccurrenceFan_mono hyz i)
      k l (ρ i k l) (σ i k l)
    · exact hOld i k l
    · exact hρ i k l
  obtain ⟨w, hzw, _htarget, hw⟩ :=
    exists_principalOccurrence_bijective_of_refined_restrictions
      (fun i k ↦ (e i k).injective) hyz hz σ hpath
  exact ⟨w, hyz.trans hzw,
    hbs.trans (principalOccurrence_source_mono hzw),
    hbt.trans (principalOccurrence_target_mono hzw), hw⟩

end FLT.Mazur.FiniteTypeRelationModel
