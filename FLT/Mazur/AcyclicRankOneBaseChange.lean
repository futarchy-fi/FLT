/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicRankOneLineCondition
public import FLT.Mazur.ProperAcyclicDirectImageRepresentation

/-!
# Intrinsic acyclic rank one under arbitrary base change

The actual direct-image condition pulls back from a proper flat family over
a locally Noetherian base. The new base is unrestricted. Surjective base
change detects the condition, using fiber cohomology and section ranks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include h hL in
/-- The intrinsic condition is represented by the actual simultaneous open on the original base. -/
theorem acyclicRankOne_iff_open_factor :
    AcyclicRankOne q ((pullback p).obj L) ↔
      ∃! a : T ⟶ (properLineAcyclicRankOneOpen f L hL).toScheme,
        a ≫ (properLineAcyclicRankOneOpen f L hL).ι = g :=
  properLineAcyclicRankOneOpen_directImage_represents f L hL h

include h hL in
/-- Acyclic rank one is preserved under arbitrary cartesian change of base. -/
theorem acyclicRankOne_baseChange (hA : AcyclicRankOne f L) :
    AcyclicRankOne q ((pullback p).obj L) := by
  have H : IsPullback (𝟙 X) f f (𝟙 S) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hI := (acyclicRankOne_iso f ((pullbackId X).app L)).mpr hA
  obtain ⟨a, ha, _⟩ := (acyclicRankOne_iff_open_factor H L hL).mp hI
  apply (acyclicRankOne_iff_open_factor h L hL).mpr
  refine ⟨g ≫ a, by dsimp only; rw [Category.assoc, ha, Category.comp_id], ?_⟩
  intro b hb
  apply (cancel_mono (properLineAcyclicRankOneOpen f L hL).ι).mp
  rw [hb, Category.assoc, ha, Category.comp_id]

include h hL in
/-- A surjective test detects the intrinsic condition without a Noetherian test base. -/
theorem acyclicRankOne_of_surjective_baseChange [Surjective g]
    (hA : AcyclicRankOne q ((pullback p).obj L)) : AcyclicRankOne f L := by
  have hv : ∀ s : S, ∀ n, Subsingleton
      (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)) := by
    intro s n
    obtain ⟨t, rfl⟩ := g.surjective s
    exact (properLine_fiber_vanishing_iff h L hL t (n + 1)).mp (hA.1 t n)
  have H : IsPullback (𝟙 X) f f (𝟙 S) := IsPullback.of_horiz_isIso ⟨by simp⟩
  apply (acyclicRankOne_iso f ((pullbackId X).app L)).mp
  have hvI := fun s n ↦ (properLine_fiber_vanishing_iff H L hL s (n + 1)).mpr (hv s n)
  refine ⟨hvI, (properLineAcyclicBaseChanged_rankOne_iff H L hL hvI).mpr ?_⟩
  intro s
  obtain ⟨t, ht⟩ := g.surjective s
  rw [properLineFiberSectionRank_baseChange H L hL s]
  change properLineFiberSectionRank f L s = 1
  rw [← ht, ← properLineFiberSectionRank_baseChange h L hL t]
  exact (properLineAcyclicBaseChanged_rankOne_iff h L hL hA.1).mp hA.2 t

include h hL in
/-- The intrinsic condition is equivalent before and after a surjective cartesian test. -/
theorem acyclicRankOne_surjective_baseChange_iff [Surjective g] :
    AcyclicRankOne q ((pullback p).obj L) ↔ AcyclicRankOne f L :=
  ⟨acyclicRankOne_of_surjective_baseChange h L hL, acyclicRankOne_baseChange h L hL⟩

end FLT.Mazur.CartierAbel
