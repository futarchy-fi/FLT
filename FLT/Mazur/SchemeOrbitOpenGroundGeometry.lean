/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOrbitOpenSelection

/-!
# Ground geometry required by open orbit selections

For an orbit map over the actual new ground, every constructed open parameter
selection is etale over that ground. Thus retaining a reflexive seed requires
an actual etale ground neighborhood in the ambient parameter scheme. This is
a necessary geometric condition, not a global coverage assertion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOrbitOpenSelection
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S Z H : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (a : Z ⟶ A.left)
  (j : pullback q.left a ⟶ H) [Mono j] [Etale q.left]
  (b : H ⟶ Z) (hb : j ≫ b = pullback.snd q.left a)
local notation "U" => parameterOpen a j
include hb

/-- The entire selected parameter open is etale over its actual new ground. -/
theorem parameterOpen_ground_etale : Etale ((U).ι ≫ b) := by
  have he : (U).ι ≫ b = projection a j := by
    rw [← MonomorphismOpenImage.lift_comp j, Category.assoc, hb]
    rfl
  rw [he]
  infer_instance

/-- A retained original seed forces an actual etale ground neighborhood of its parameter. -/
theorem seed_has_etale_ground_neighborhood (z : Z) (hz : z ∈ seedOpen e a j) :
    ∃ V : H.Opens, j (SchemeRelationSplitOrbit.sectionMap e a z) ∈ V ∧
      Etale (V.ι ≫ b) :=
  ⟨U, hz, parameterOpen_ground_etale a j b hb⟩

/-- Without such a ground neighborhood the original reflexive seed cannot be retained. -/
theorem seed_not_mem_of_no_etale_ground_neighborhood (z : Z)
    (hn : ∀ V : H.Opens, j (SchemeRelationSplitOrbit.sectionMap e a z) ∈ V →
      ¬ Etale (V.ι ≫ b)) : z ∉ seedOpen e a j := by
  intro hz
  obtain ⟨V, hv, he⟩ := seed_has_etale_ground_neighborhood e a j b hb z hz
  exact hn V hv he

/-- Actual unramified ground geometry makes the whole original orbit map open. -/
theorem chart_isOpenImmersion_of_ground_unramified
    [FormallyUnramified b] [LocallyOfFiniteType b] : IsOpenImmersion j := by
  let _ : Etale (j ≫ b) := by rw [hb]; infer_instance
  let _ : Etale j := Etale.of_comp j b
  exact IsOpenImmersion.of_flat_of_mono j

/-- Under that genuine ground condition every original seed is retained. -/
theorem seedOpen_eq_top_of_ground_unramified
    [FormallyUnramified b] [LocallyOfFiniteType b] : seedOpen e a j = ⊤ := by
  let _ := chart_isOpenImmersion_of_ground_unramified a j b hb
  apply top_le_iff.mp
  intro z _
  change SchemeRelationSplitOrbit.sectionMap e a z ∈ MonomorphismOpenImage.sourceOpen j
  rw [MonomorphismOpenImage.sourceOpen_eq_top]
  trivial

end FLT.Mazur.SchemeOrbitOpenSelection
