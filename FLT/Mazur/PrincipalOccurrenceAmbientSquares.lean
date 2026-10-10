/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOpenEmbeddings

/-!
# Ambient coordinate squares for shared overlap embeddings

Occurrence maps give maps from the full ambient chart rings. They retain
the original coordinates and commute with every refinement. Consequently
the shared overlap open immersions form commuting scheme squares as well.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}

/-- Restrict the ambient chart ring into an occurrence's shared target. -/
def principalOccurrenceAmbientHom (x : PrincipalOccurrenceStage dst a b f) (i : ι) (e : J i) :
    Stage R (A i) (x.source i) →ₐ[R]
      PrincipalStage R (B (dst i e)) (b (dst i e)) (x.target (dst i e)) :=
  (x.hom i e).comp (IsScalarTower.toAlgHom R _ _)

/-- Ambient restriction maps recover the specified original coordinate maps. -/
theorem principalOccurrenceAmbientHom_fac (x : PrincipalOccurrenceStage dst a b f)
    (i : ι) (e : J i) :
    (principalStageMap R (B (dst i e)) (b (dst i e)) (x.target (dst i e))).comp
      (principalOccurrenceAmbientHom x i e) =
    ((f i e).comp (IsScalarTower.toAlgHom R (A i) (Localization.Away (a i e)))).comp
      (stageMap R (A i) (x.source i)) := by
  apply AlgHom.ext
  intro z
  have h := AlgHom.congr_fun (x.fac i e)
    (algebraMap (Stage R (A i) (x.source i)) (PrincipalStage R (A i) (a i e) (x.source i)) z)
  simpa only [principalOccurrenceAmbientHom, AlgHom.comp_apply,
    IsScalarTower.toAlgHom_apply, principalStageMap_algebraMap] using h

/-- The complete ambient ring square commutes under each occurrence refinement. -/
theorem principalOccurrenceAmbientHom_comm {x y : PrincipalOccurrenceStage dst a b f}
    (hxy : x ≤ y) (i : ι) (e : J i) :
    (principalOccurrenceAmbientHom y i e).comp
      (FiniteRelationModel.transition R (relationIdeal R (A i))
        (principalOccurrence_source_mono hxy i)) =
    (principalTransition (b (dst i e)) (principalOccurrence_target_mono hxy (dst i e))).comp
      (principalOccurrenceAmbientHom x i e) := by
  apply AlgHom.ext
  intro z
  have h := AlgHom.congr_fun (principalOccurrence_hom_comm hxy i e)
    (algebraMap (Stage R (A i) (x.source i)) (PrincipalStage R (A i) (a i e) (x.source i)) z)
  change y.hom i e (principalTransition (a i e) _ (algebraMap _ _ z)) = _ at h
  rw [FiniteRelationLocalization.transition_algebraMap] at h
  exact h

/-- The shared overlap embedding is the spectrum of its explicit ambient coordinate map. -/
theorem principalOccurrenceOpen_eq_spec (x : PrincipalOccurrenceStage dst a b f)
    (hx : ∀ i e, Function.Bijective (x.hom i e)) (i : ι) (e : J i) :
    principalOccurrenceOpen x hx i e =
      Spec.map (CommRingCat.ofHom (principalOccurrenceAmbientHom x i e).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (x.hom i e).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap _ (PrincipalStage R (A i) (a i e) (x.source i)))) = _
  simp only [← Spec.map_comp]
  rfl

/-- Shared overlap embeddings commute with the chart and overlap scheme transitions. -/
theorem principalOccurrenceOpen_comm {x y : PrincipalOccurrenceStage dst a b f}
    (hx : ∀ i e, Function.Bijective (x.hom i e))
    (hy : ∀ i e, Function.Bijective (y.hom i e)) (hxy : x ≤ y) (i : ι) (e : J i) :
    Spec.map (CommRingCat.ofHom (principalTransition (b (dst i e))
      (principalOccurrence_target_mono hxy (dst i e))).toRingHom) ≫
        principalOccurrenceOpen x hx i e =
    principalOccurrenceOpen y hy i e ≫ Spec.map (CommRingCat.ofHom
      (FiniteRelationModel.transition R (relationIdeal R (A i))
        (principalOccurrence_source_mono hxy i)).toRingHom) := by
  rw [principalOccurrenceOpen_eq_spec, principalOccurrenceOpen_eq_spec]
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (principalOccurrenceAmbientHom_comm hxy i e).symm

end FLT.Mazur.FiniteTypeRelationModel
