/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameTestCartesian
public import FLT.Mazur.RelativeFrameClosedRankCompleteness

/-!
# Complete frames split full original pullbacks over arbitrary coefficients

A frame whose image lies in the closed complete locus splits the entire
original pullback as a finite coproduct of the test scheme. In particular,
closed rank bounds suffice, even for nonreduced tests and at residual points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {T : Scheme} {b : T ⟶ S}
  (t : Over.mk b ⟶ distinctScheme E I)

/-- Complete image forces every original pullback point onto a coordinate section. -/
theorem testSection_cover_of_complete (ht : Set.range t.left ⊆ completeLocus E I)
    (z : ↥(pullback E.hom b)) : ∃ i : I, z ∈ Set.range (testSection E I t i) := by
  have hc := ht (Set.mem_range_self (pullback.snd E.hom b z))
  have hz : framedProjection E I (testToFramed E I t z) =
      t.left (pullback.snd E.hom b z) :=
    congrArg (fun f ↦ f z) (testToFramed_projection E I t)
  obtain ⟨i, hi⟩ := (mem_completeLocus_iff_sections E I _).mp hc _ hz
  refine ⟨i, ?_⟩
  have H := testToFramed_coordinate_isPullback E I t i
  have hr : Set.range (testSection E I t i) =
      testToFramed E I t ⁻¹' Set.range (framedSection E I i) := by
    rw [← H.isoPullback_hom_snd]
    exact (H.isoPullback.hom.surjective.range_comp _).trans
      (Scheme.Pullback.range_snd (framedSection E I i) (testToFramed E I t))
  rw [hr]
  exact ⟨t.left (pullback.snd E.hom b z), hi⟩

/-- The actual coordinate comparison is an isomorphism over every complete test. -/
theorem testComparison_isIso_of_complete (ht : Set.range t.left ⊆ completeLocus E I) :
    IsIso (testComparison E I t) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro z
  obtain ⟨i, x, hx⟩ := testSection_cover_of_complete E I t ht z
  refine ⟨(Sigma.ι (fun _ : I ↦ T) i) x, ?_⟩
  exact (congrArg (fun f ↦ f x) (testComparison_component E I t i)).trans hx

/-- The entire original pullback splits, retaining the test scheme's nilpotents. -/
def completeTestIso (ht : Set.range t.left ⊆ completeLocus E I) :
    (∐ fun _ : I ↦ T) ≅ pullback E.hom b := by
  let _ := testComparison_isIso_of_complete E I t ht
  exact asIso (testComparison E I t)

/-- The split comparison keeps each original coordinate, not only its geometric points. -/
@[reassoc] theorem completeTestIso_component (ht : Set.range t.left ⊆ completeLocus E I)
    (i : I) :
    Sigma.ι (fun _ : I ↦ T) i ≫ (completeTestIso E I t ht).hom = testSection E I t i :=
  testComparison_component E I t i

variable [QuasiCompact E.hom]

/-- Every frame supported on a closed rank bound splits the full original pullback. -/
def rankAtMostTestIso (n : ℕ) (a : Over.mk b ⟶ distinctScheme E (Fin n))
    (hb : Set.range b ⊆ rankAtMost E n) : (∐ fun _ : Fin n ↦ T) ≅ pullback E.hom b :=
  completeTestIso E (Fin n) a (frame_range_complete_of_rankAtMost E n a hb)

end FLT.Mazur.RelativeOrderedTuples
