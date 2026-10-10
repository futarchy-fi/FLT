/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Restricting inverse limits to an upper interval

A directed preorder can be restricted above any chosen stage without changing
an inverse limit. The restricted index has a distinguished terminal stage
in its opposite, useful for pulling back a cover of that stage.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u v w

variable {I : Type u} [Preorder I]

/-- The inclusion of stages above a fixed bound. -/
def upperStageInclusion (i : I) : Set.Ici i ⥤ I :=
  (Subtype.mono_coe (· ∈ Set.Ici i)).functor

/-- Every two stages above a bound have a common stage above that bound. -/
theorem upperStage_directed [IsDirectedOrder I] (i : I) :
    IsDirectedOrder (Set.Ici i) where
  directed x y := by
    obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x.val y.val
    exact ⟨⟨z, x.property.trans hxz⟩, hxz, hyz⟩

/-- The upper-stage inclusion is final. -/
theorem upperStageInclusion_final [IsDirectedOrder I] (i : I) :
    (upperStageInclusion i).Final := by
  let _ := upperStage_directed i
  apply (Subtype.mono_coe (· ∈ Set.Ici i)).final_functor_iff.mpr
  intro j
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact ⟨⟨k, hik⟩, hjk⟩

variable {C : Type v} [Category.{w} C] {F : Iᵒᵖ ⥤ C}

/-- An inverse limit remains a limit after restriction above any stage. -/
def upperStageIsLimit [IsDirectedOrder I] (i : I) {c : Cone F} (hc : IsLimit c) :
    IsLimit (c.whisker (upperStageInclusion i).op) := by
  let _ := upperStageInclusion_final i
  exact (Functor.Initial.isLimitWhiskerEquiv (upperStageInclusion i).op c).symm hc

/-- Equality on an upper interval detects equality into an inverse limit. -/
theorem upperStage_hom_ext [IsDirectedOrder I] (i : I) {c : Cone F} (hc : IsLimit c)
    {Y : C} {a b : Y ⟶ c.pt}
    (h : ∀ j : Set.Ici i, a ≫ c.π.app (.op j.val) = b ≫ c.π.app (.op j.val)) :
    a = b := by
  apply (upperStageIsLimit i hc).hom_ext
  intro j
  exact h j.unop

end FLT.Mazur.Approximation
