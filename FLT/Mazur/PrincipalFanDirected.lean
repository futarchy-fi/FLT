/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanStages

/-!
# Common refinements with one shared ambient chart

All coordinate squares can be imposed by enlarging only the target stages.
Consequently distinct denominators do not obstruct directed refinement of
the full fan index or arbitrary lower bounds on its ambient relations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  {a : ι → A} {b : ∀ i, B i}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away (b i)}

/-- Impose every old square while retaining the new shared source stage exactly. -/
theorem exists_principalFanStage_compare (x z : PrincipalFanStage a b f)
    (hs : x.source ≤ z.source) (ht : x.target ≤ z.target) :
    ∃ w : PrincipalFanStage a b f, x ≤ w ∧ z ≤ w ∧ w.source = z.source := by
  have he (i) : (principalStageMap R (B i) (b i) (z.target i)).comp
        ((z.hom i).comp (principalTransition (a i) hs)) =
      (principalStageMap R (B i) (b i) (z.target i)).comp
        ((principalTransition (b i) (ht i)).comp (x.hom i)) := by
    rw [← AlgHom.comp_assoc, z.fac, AlgHom.comp_assoc, principalStageMap_transition,
      ← AlgHom.comp_assoc, principalStageMap_transition, x.fac]
  choose q hq hc using fun i ↦ exists_principal_hom_eq (b i) (z.target i)
    ((z.hom i).comp (principalTransition (a i) hs))
    ((principalTransition (b i) (ht i)).comp (x.hom i)) (he i)
  let w : PrincipalFanStage a b f :=
    { source := z.source
      target := q
      hom i := (principalTransition (b i) (hq i)).comp (z.hom i)
      fac i := by rw [← AlgHom.comp_assoc, principalStageMap_transition, z.fac] }
  refine ⟨w, ⟨hs, fun i ↦ ⟨hs, (ht i).trans (hq i), ?_⟩⟩,
    ⟨le_rfl, fun i ↦ ⟨le_rfl, hq i, ?_⟩⟩, rfl⟩
  · change ((principalTransition (b i) (hq i)).comp (z.hom i)).comp
        (principalTransition (a i) hs) = _
    rw [AlgHom.comp_assoc, hc, ← AlgHom.comp_assoc, principalTransition_comp]
    rfl
  · change ((principalTransition (b i) (hq i)).comp (z.hom i)).comp
        (principalTransition (a i) (le_refl z.source)) = _
    rw [principalTransition_refl, AlgHom.comp_id]
    rfl

/-- A fan admits a commuting refinement above arbitrary ambient and target bounds. -/
theorem exists_principalFanStage_extension (x : PrincipalFanStage a b f)
    (s : Finset (relationIdeal R A)) (t : ∀ i, Finset (relationIdeal R (B i))) :
    ∃ w : PrincipalFanStage a b f, x ≤ w ∧ s ≤ w.source ∧ t ≤ w.target := by
  classical
  obtain ⟨z, hzS, hzT⟩ := exists_principalFanStage (a := a) (b := b) (f := f)
    (x.source ∪ s) (fun i ↦ x.target i ∪ t i)
  have hxs : x.source ≤ z.source := hzS ▸ Finset.subset_union_left
  have hxt : x.target ≤ z.target := fun i ↦ Finset.subset_union_left.trans (hzT i)
  obtain ⟨w, hxw, hzw, hw⟩ := exists_principalFanStage_compare x z hxs hxt
  refine ⟨w, hxw, ?_, fun i ↦ ?_⟩
  · rw [hw, hzS]
    exact Finset.subset_union_right
  · exact Finset.subset_union_right.trans ((hzT i).trans (principalFan_target_mono hzw i))

/-- Different denominators still permit a common commuting refinement. -/
instance principalFanStageDirected : IsDirectedOrder (PrincipalFanStage a b f) where
  directed x y := by
    obtain ⟨z, hxz, hyS, hyT⟩ := exists_principalFanStage_extension x y.source y.target
    obtain ⟨w, hyw, hzw, _⟩ := exists_principalFanStage_compare y z hyS hyT
    exact ⟨w, hxz.trans hzw, hyw⟩

/-- Fan stages form a filtered category. -/
instance principalFanStageFiltered : CategoryTheory.IsFiltered (PrincipalFanStage a b f) :=
  inferInstance

end FLT.Mazur.FiniteTypeRelationModel
