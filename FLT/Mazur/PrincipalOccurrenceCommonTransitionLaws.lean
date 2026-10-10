/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonTransition

/-!
# Identity, composition, and recovery for common-union transitions

The affine transition laws pass to the canonical full union maps by
cancelling their open inclusions into the ambient chart.
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
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))

variable {y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)}
  (hxy : x ≤ y) (hy : ∀ i k, Function.Bijective (y.hom i k))

/-- Ambient chart transitions compose in the inverse-system direction. -/
@[reassoc] theorem principalOccurrenceAmbientTransition_comp
    {z : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)}
    (hyz : y ≤ z) (i : ι) :
    principalOccurrenceAmbientTransition hyz i ≫ principalOccurrenceAmbientTransition hxy i =
      principalOccurrenceAmbientTransition (hxy.trans hyz) i := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom
    (FiniteRelationModel.transition_comp R (relationIdeal R (A i))
      (principalOccurrence_source_mono hxy i) (principalOccurrence_source_mono hyz i)))

/-- A reflexive ambient transition is the identity. -/
theorem principalOccurrenceAmbientTransition_id (i : ι) :
    principalOccurrenceAmbientTransition (le_refl x) i = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom _) = _
  trans Spec.map (𝟙 (.of (Stage R (A i) (x.source i))))
  · congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  · exact Spec.map_id _

/-- Original chart projections commute with refinement. -/
@[reassoc] theorem principalOccurrenceAmbientProjection_transition (i : ι) :
    principalOccurrenceAmbientProjection e y i ≫ principalOccurrenceAmbientTransition hxy i =
      principalOccurrenceAmbientProjection e x i := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom
    (stageMap_transition R (A i) (principalOccurrence_source_mono hxy i)))

/-- A reflexive common-union transition is the identity. -/
theorem principalOccurrenceCommonTransition_id (i t : ι) :
    principalOccurrenceCommonTransition e x hx (le_refl x) hx i t = 𝟙 _ := by
  apply (cancel_mono (principalOccurrenceCommonUnion e x hx i t).ι).mp
  rw [principalOccurrenceCommonTransition_fac,
    principalOccurrenceAmbientTransition_id, Category.comp_id, Category.id_comp]

/-- Common-union transitions compose on their entire domains. -/
@[reassoc] theorem principalOccurrenceCommonTransition_comp
    {z : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)}
    (hyz : y ≤ z) (hz : ∀ i k, Function.Bijective (z.hom i k)) (i t : ι) :
    principalOccurrenceCommonTransition e y hy hyz hz i t ≫
        principalOccurrenceCommonTransition e x hx hxy hy i t =
      principalOccurrenceCommonTransition e x hx (hxy.trans hyz) hz i t := by
  apply (cancel_mono (principalOccurrenceCommonUnion e x hx i t).ι).mp
  rw [Category.assoc, principalOccurrenceCommonTransition_fac,
    principalOccurrenceCommonTransition_fac_assoc, principalOccurrenceCommonTransition_fac,
    principalOccurrenceAmbientTransition_comp]

/-- The original full-union projections commute with every refinement. -/
@[reassoc] theorem principalOccurrenceCommonProjection_transition (i t : ι) :
    principalOccurrenceCommonProjection e y hy i t ≫
        principalOccurrenceCommonTransition e x hx hxy hy i t =
      principalOccurrenceCommonProjection e x hx i t := by
  apply (cancel_mono (principalOccurrenceCommonUnion e x hx i t).ι).mp
  rw [Category.assoc, principalOccurrenceCommonTransition_fac,
    principalOccurrenceCommonProjection_fac_assoc, principalOccurrenceCommonProjection_fac,
    principalOccurrenceAmbientProjection_transition]

end FLT.Mazur.FiniteTypeRelationModel
