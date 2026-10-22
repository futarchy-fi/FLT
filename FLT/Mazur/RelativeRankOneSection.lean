/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameTestSplitting
public import FLT.Mazur.RelativeSingletonFrame

/-!
# Full rank-one pullbacks with an original section

A section over a test supported on the closed rank-one bound accounts for
the entire original pullback. The resulting isomorphism retains nilpotents
and does not require the test to be affine, reduced, or Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] {b : T ⟶ S} (a : Over.mk b ⟶ E)
  (hb : Set.range b ⊆ rankAtMost E 1)
include a hb

/-- The supplied original coordinate covers the full rank-one pullback. -/
theorem singleton_testSection_surjective :
    Function.Surjective (testSection E (Fin 1) (singletonFrame E a) 0) := by
  intro z
  change z ∈ Set.range (testSection E (Fin 1) (singletonFrame E a) 0)
  obtain ⟨i, hi⟩ := testSection_cover_of_complete E (Fin 1) (singletonFrame E a)
    (frame_range_complete_of_rankAtMost E 1 (singletonFrame E a) hb) z
  simpa only [Subsingleton.elim i (0 : Fin 1)] using hi

/-- No infinitesimal directions remain outside the singleton coordinate section. -/
theorem singleton_testSection_isIso :
    IsIso (testSection E (Fin 1) (singletonFrame E a) 0) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  exact ⟨inferInstance, ⟨singleton_testSection_surjective E a hb⟩⟩

/-- The entire original source is isomorphic to its rank-one coefficient test. -/
theorem rankOne_pullback_isIso : IsIso (pullback.snd E.hom b) := by
  let _ := singleton_testSection_isIso E a hb
  exact isIso_of_hom_comp_eq_id (testSection E (Fin 1) (singletonFrame E a) 0)
    (testSection_snd E (Fin 1) (singletonFrame E a) 0)

/-- The original first projection is exactly the section followed by the coefficient map. -/
theorem rankOne_pullback_fst :
    pullback.fst E.hom b = pullback.snd E.hom b ≫ a.left := by
  let _ := singleton_testSection_isIso E a hb
  apply (cancel_epi (testSection E (Fin 1) (singletonFrame E a) 0)).mp
  rw [testSection_fst, testSection_snd_assoc]
  exact congrArg Over.Hom.left (singletonFrame_coordinate E a 0)

/-- Every full original arrow over the test is its prescribed singleton section. -/
theorem rankOne_arrow_eq {U : Scheme.{0}} (d : U ⟶ E.left) (v : U ⟶ T)
    (h : d ≫ E.hom = v ≫ b) : d = v ≫ a.left := by
  let w := pullback.lift d v h
  have he := congrArg (fun f ↦ w ≫ f) (rankOne_pullback_fst E a hb)
  simpa only [Category.assoc, w, pullback.lift_fst, pullback.lift_snd_assoc] using he

end FLT.Mazur.RelativeOrderedTuples
