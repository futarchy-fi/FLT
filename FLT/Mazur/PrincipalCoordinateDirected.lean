/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalCoordinateStages
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Directed refinement of finite principal coordinate models

Any two finite lifts have a common commuting refinement. Both chart indices
can be made arbitrarily large. All commutativity equations are obtained by
finite equality detection, rather than assumed as approximation data.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
  {a : A} {b : B} {f : Localization.Away a →ₐ[R] Localization.Away b}

/-- Once both relation sets dominate an old lift, impose its commuting square. -/
theorem exists_principalMapStage_compare (x z : PrincipalMapStage a b f)
    (hs : x.source ≤ z.source) (ht : x.target ≤ z.target) :
    ∃ w : PrincipalMapStage a b f, x ≤ w ∧ z ≤ w ∧ w.source = z.source := by
  have he : (principalStageMap R B b z.target).comp
        (z.hom.comp (principalTransition a hs)) =
      (principalStageMap R B b z.target).comp
        ((principalTransition b ht).comp x.hom) := by
    rw [← AlgHom.comp_assoc, z.fac, AlgHom.comp_assoc, principalStageMap_transition,
      ← AlgHom.comp_assoc, principalStageMap_transition, x.fac]
  obtain ⟨q, hq, hcomm⟩ := exists_principal_hom_eq b z.target
    (z.hom.comp (principalTransition a hs)) ((principalTransition b ht).comp x.hom) he
  let w : PrincipalMapStage a b f :=
    { source := z.source
      target := q
      hom := (principalTransition b hq).comp z.hom
      fac := by rw [← AlgHom.comp_assoc, principalStageMap_transition, z.fac] }
  refine ⟨w, ⟨hs, ht.trans hq, ?_⟩, ⟨le_rfl, hq, ?_⟩, rfl⟩
  · change ((principalTransition b hq).comp z.hom).comp (principalTransition a hs) = _
    rw [AlgHom.comp_assoc, hcomm, ← AlgHom.comp_assoc, principalTransition_comp]
  · change ((principalTransition b hq).comp z.hom).comp
        (principalTransition a (le_refl z.source)) = _
    rw [principalTransition_refl, AlgHom.comp_id]

/-- A lift admits a commuting extension beyond arbitrary bounds on both charts. -/
theorem exists_principalMapStage_extension (x : PrincipalMapStage a b f)
    (s : Finset (relationIdeal R A)) (t : Finset (relationIdeal R B)) :
    ∃ w : PrincipalMapStage a b f, x ≤ w ∧ s ≤ w.source ∧ t ≤ w.target := by
  classical
  obtain ⟨z, hzS, hzT⟩ := exists_principalMapStage (a := a) (b := b) (f := f)
    (x.source ∪ s) (x.target ∪ t)
  have hxs : x.source ≤ z.source := hzS ▸ Finset.subset_union_left
  have hxt : x.target ≤ z.target := Finset.subset_union_left.trans hzT
  obtain ⟨w, hxw, hzw, hw⟩ := exists_principalMapStage_compare x z hxs hxt
  refine ⟨w, hxw, ?_, ?_⟩
  · rw [hw, hzS]
    exact Finset.subset_union_right
  · exact Finset.subset_union_right.trans (hzT.trans hzw.choose_spec.choose)

/-- Two finite lifts of the same original map have a common commuting refinement. -/
instance principalMapStageDirected : IsDirectedOrder (PrincipalMapStage a b f) where
  directed x y := by
    obtain ⟨z, hxz, hyS, hyT⟩ := exists_principalMapStage_extension x y.source y.target
    obtain ⟨w, hyw, hzw, _⟩ := exists_principalMapStage_compare y z hyS hyT
    exact ⟨w, hxz.trans hzw, hyw⟩

/-- The category of finite coordinate models is filtered. -/
instance principalMapStageFiltered :
    CategoryTheory.IsFiltered (PrincipalMapStage a b f) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel
