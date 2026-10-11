/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineGlobalRankOneCriterion

/-!
# The simultaneous open represents the actual acyclic direct-image line condition

The fiber-cohomology construction now represents acyclicity together with
local rank one of the actual direct image on every test scheme. In particular,
the actual restricted family's direct image on the constructed open is a line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve
variable {X S : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The simultaneous open represents acyclicity and actual direct-image rank one on all tests. -/
theorem properLineAcyclicRankOneOpen_directImage_represents {P T : Scheme.{0}}
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g) :
    ((∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) ∧
        LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L))) ↔
      ∃! a : T ⟶ (properLineAcyclicRankOneOpen f L hL).toScheme,
        a ≫ (properLineAcyclicRankOneOpen f L hL).ι = g := by
  rw [← properLineAcyclicRankOneOpen_represents f L hL h]
  constructor
  · rintro ⟨hv, hn⟩ t
    exact ⟨hv t, (properLineAcyclicBaseChanged_rankOne_iff h L hL hv).mp hn t⟩
  · intro ht
    have hv := fun t ↦ (ht t).1
    exact ⟨hv, (properLineAcyclicBaseChanged_rankOne_iff h L hL hv).mpr
      (fun t ↦ (ht t).2)⟩

/-- The actual universal family on the simultaneous open has a rank-one direct image. -/
theorem properLineAcyclicRankOneOpen_directImage_rankOne :
    LocallyFreeRankOne
      ((pushforward (f ∣_ properLineAcyclicRankOneOpen f L hL)).obj
        ((pullback (f ⁻¹ᵁ properLineAcyclicRankOneOpen f L hL).ι).obj L)) := by
  apply ((properLineAcyclicRankOneOpen_directImage_represents f L hL
    (isPullback_morphismRestrict f (properLineAcyclicRankOneOpen f L hL)).flip).mpr ?_).2
  exact ⟨𝟙 _, Category.id_comp _, fun a ha ↦ (cancel_mono _).mp (by simpa using ha)⟩

/-- On a globally acyclic family the global rank-one open represents the actual line condition. -/
theorem properLineGlobalRankOneOpen_directImage_represents
    (hV : ∀ s : S, ∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)))
    {P T : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
    (h : IsPullback p q f g) :
    LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)) ↔
      ∃! a : T ⟶ (properLineGlobalRankOneOpen f L hL hV).toScheme,
        a ≫ (properLineGlobalRankOneOpen f L hL hV).ι = g := by
  rw [properLineGlobalRankOne_iff h L hL hV]
  constructor
  · intro ht
    have hr : Set.range g ⊆ Set.range (properLineGlobalRankOneOpen f L hL hV).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      exact ht t
    refine ⟨IsOpenImmersion.lift _ g hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    intro b hb
    rw [← cancel_mono (properLineGlobalRankOneOpen f L hL hV).ι, hb,
      IsOpenImmersion.lift_fac]
  · rintro ⟨a, ha, _⟩ t
    rw [← ha]
    exact (a t).property

end FLT.Mazur.LineSectionBaseChange
