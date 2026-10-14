/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfTargetOpen

/-!
# Dense fppf images of flat projections without reducedness

An actual flat, finitely presented, dominant projection has a dense fppf
image on the unchanged target. This also holds after every open restriction,
without using generic flatness or requiring an integral source or target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfTargetOpen
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [Flat f]

/-- For a flat projection the constructed fppf region is exactly the original image. -/
theorem coe_locus_of_flat : (locus f : Set Y) = Set.range f := by
  rw [coe_locus, SchemeFlatTargetOpen.locus_top]
  exact Set.inter_univ _

variable [IsDominant f]

/-- Dominance gives density on arbitrary targets, including nonreduced targets. -/
theorem dense_of_flat : Dense (locus f : Set Y) := by
  rw [coe_locus_of_flat]
  exact f.denseRange

/-- Flatness and dominance persist over an actual target open with all nilpotents retained. -/
theorem dense_open_baseChange_of_flat {Z : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j] :
    Dense (locus (pullback.snd f j) : Set Z) := by
  let _ : IsDominant (pullback.snd f j) :=
    IsZariskiLocalAtTarget.of_isPullback (IsPullback.of_hasPullback f j) inferInstance
  exact dense_of_flat (pullback.snd f j)

/-- Passing to the represented fppf image loses no nonempty open of the original target. -/
theorem nonempty_open_baseChange_iff_of_flat {Z : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] :
    (locus (pullback.snd f j) : Set Z).Nonempty ↔ Nonempty Z := by
  refine ⟨fun ⟨z, _⟩ ↦ ⟨z⟩, fun hZ ↦ ?_⟩
  let _ := hZ
  exact (dense_open_baseChange_of_flat f j).nonempty

end FLT.Mazur.SchemeFppfTargetOpen
