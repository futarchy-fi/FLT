/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineGlobalAcyclicOpen

/-!
# The global acyclic open represents fiber vanishing on all test schemes

The factorization criterion uses actual cohomology on every test fiber.
The test base need not be Noetherian, affine, or reduced. The lift into the
constructed open is unique as a scheme morphism.
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
  {P T : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
  (h : IsPullback p q f g)

include h in
/-- Fiber acyclicity on an arbitrary test is exactly pointwise membership in the global open. -/
theorem properLineTest_acyclic_iff :
    (∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) ↔
      ∀ t : T, g t ∈ properLineGlobalAcyclicOpen f L hL :=
  forall_congr' fun t ↦ forall_congr' fun n ↦
    properLine_fiber_vanishing_iff h L hL t (n + 1)

include h in
/-- The actual acyclicity open represents the geometric fiber condition on every test scheme. -/
theorem properLineGlobalAcyclicOpen_represents :
    (∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) ↔
      ∃! a : T ⟶ (properLineGlobalAcyclicOpen f L hL).toScheme,
        a ≫ (properLineGlobalAcyclicOpen f L hL).ι = g := by
  rw [properLineTest_acyclic_iff f L hL h]
  constructor
  · intro ht
    have hr : Set.range g ⊆ Set.range (properLineGlobalAcyclicOpen f L hL).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      exact ht t
    refine ⟨IsOpenImmersion.lift _ g hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    intro b hb
    rw [← cancel_mono (properLineGlobalAcyclicOpen f L hL).ι, hb,
      IsOpenImmersion.lift_fac]
  · rintro ⟨a, ha, _⟩ t
    rw [← ha]
    exact (a t).property

/-- The family restricted to the constructed open has all its actual fibers acyclic. -/
theorem properLineGlobalAcyclicOpen_fibers
    (t : (properLineGlobalAcyclicOpen f L hL).toScheme) (n : ℕ) :
    Subsingleton (ModuleH
      ((pullback ((f ∣_ properLineGlobalAcyclicOpen f L hL).fiberι t)).obj
        ((pullback (f ⁻¹ᵁ properLineGlobalAcyclicOpen f L hL).ι).obj L)) (n + 1)) :=
  (properLineTest_acyclic_iff f L hL
    (isPullback_morphismRestrict f (properLineGlobalAcyclicOpen f L hL)).flip).mpr
      (fun s ↦ s.property) t n

end FLT.Mazur.LineSectionBaseChange
