/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameScalarCompleteness
public import FLT.Mazur.RelativeTupleCompletenessLocus

/-!
# Geometric completeness equals the actual residual-scheme locus

The field-valued definition of completeness agrees exactly with the existing
closed locus cut out by absence of points in the original residual scheme.
The comparison uses the entire original fiber and cartesian coordinate squares.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {K : Type} [Field K] {b : Spec (.of K) ⟶ S}
  (t : Over.mk b ⟶ distinctScheme E I)

/-- Map the whole original geometric fiber to the universal framed source. -/
def geometricToFramed : pullback E.hom b ⟶ framedSource E I :=
  pullback.lift (pullback.fst E.hom b) (pullback.snd E.hom b ≫ t.left)
    (by rw [Category.assoc, t.w]; exact pullback.condition)

omit [Etale E.hom] in
@[reassoc] theorem geometricToFramed_fst :
    geometricToFramed E I t ≫ pullback.fst E.hom (distinctScheme E I).hom =
      pullback.fst E.hom b := pullback.lift_fst _ _ _

omit [Etale E.hom] in
@[reassoc] theorem geometricToFramed_projection :
    geometricToFramed E I t ≫ framedProjection E I = pullback.snd E.hom b ≫ t.left :=
  pullback.lift_snd _ _ _

omit [Etale E.hom] in
/-- The entire original geometric fiber is the actual fiber of the framed projection. -/
theorem geometricToFramed_isPullback :
    IsPullback (geometricToFramed E I t) (pullback.snd E.hom b)
      (framedProjection E I) t.left := by
  apply IsPullback.of_right (h₁₂ := pullback.fst E.hom (distinctScheme E I).hom)
    (h₂₂ := (distinctScheme E I).hom)
  · rw [geometricToFramed_fst, t.w]
    exact IsPullback.of_hasPullback E.hom b
  · exact geometricToFramed_projection E I t
  · exact IsPullback.of_hasPullback E.hom (distinctScheme E I).hom

omit [Etale E.hom] in
/-- Each original geometric coordinate is the pullback of its universal section. -/
@[reassoc] theorem geometricToFramed_coordinate (i : I) :
    geometricCoordinate E I t i ≫ geometricToFramed E I t = t.left ≫ framedSection E I i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, geometricToFramed_fst, framedSection_original,
      geometricCoordinate_fst]
    rfl
  · change _ ≫ framedProjection E I = _ ≫ framedProjection E I
    simp only [Category.assoc, geometricToFramed_projection, geometricCoordinate_snd_assoc,
      framedSection_projection, Category.comp_id]

omit [Etale E.hom] in
/-- The coordinate comparison is cartesian, including its scheme structure. -/
theorem geometricToFramed_coordinate_isPullback (i : I) :
    IsPullback t.left (geometricCoordinate E I t i) (framedSection E I i)
      (geometricToFramed E I t) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd E.hom b) (v₂₂ := framedProjection E I)
  · simp only [geometricCoordinate_snd, framedSection_projection]
    exact IsPullback.of_id_snd
  · exact (geometricToFramed_coordinate E I t i).symm
  · exact geometricToFramed_isPullback E I t

/-- The field-valued completeness definition agrees exactly with the residual-scheme locus. -/
theorem geometric_complete_iff_mem_completeLocus :
    Function.Bijective (fun i ↦ geometricCoordinate E I t i default) ↔
      t.left (default : Spec (.of K)) ∈ completeLocus E I := by
  rw [mem_completeLocus_iff_sections]
  constructor
  · intro ht y hy
    have H := geometricToFramed_isPullback E I t
    have hr : Set.range (geometricToFramed E I t) =
        framedProjection E I ⁻¹' Set.range t.left := by
      rw [← H.isoPullback_hom_fst]
      exact (H.isoPullback.hom.surjective.range_comp _).trans
        (Scheme.Pullback.range_fst (framedProjection E I) t.left)
    have hm : y ∈ Set.range (geometricToFramed E I t) := by
      rw [hr]
      exact ⟨(default : Spec (.of K)), hy.symm⟩
    obtain ⟨z, hz⟩ := hm
    obtain ⟨i, hi⟩ := ht.2 z
    dsimp only at hi
    refine ⟨i, ?_⟩
    have hc := congrArg (fun f ↦ f default) (geometricToFramed_coordinate E I t i)
    rw [Scheme.Hom.comp_apply, hi, hz, Scheme.Hom.comp_apply] at hc
    exact hc.symm
  · intro ht
    refine ⟨geometricCoordinate_point_injective E I t, ?_⟩
    intro z
    have hz : framedProjection E I (geometricToFramed E I t z) =
        t.left (default : Spec (.of K)) := by
      rw [← Scheme.Hom.comp_apply, geometricToFramed_projection, Scheme.Hom.comp_apply]
      exact congrArg t.left (Subsingleton.elim (α := Spec (.of K)) _ _)
    obtain ⟨i, hi⟩ := ht (geometricToFramed E I t z) hz
    have H := geometricToFramed_coordinate_isPullback E I t i
    have hr : Set.range (geometricCoordinate E I t i) =
        geometricToFramed E I t ⁻¹' Set.range (framedSection E I i) := by
      rw [← H.isoPullback_hom_snd]
      exact (H.isoPullback.hom.surjective.range_comp _).trans
        (Scheme.Pullback.range_snd (framedSection E I i) (geometricToFramed E I t))
    have hm : z ∈ Set.range (geometricCoordinate E I t i) := by
      rw [hr]
      exact ⟨t.left (default : Spec (.of K)), hi⟩
    obtain ⟨a, ha⟩ := hm
    exact ⟨i, (congrArg (geometricCoordinate E I t i) (Subsingleton.elim default a)).trans ha⟩

end FLT.Mazur.RelativeOrderedTuples
