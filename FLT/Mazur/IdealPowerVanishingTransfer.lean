/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EventualTwistVanishing
public import FLT.Mazur.IdealPowerGenericComparison
public import FLT.Mazur.FinitePushforwardIdealVanishing

/-!
# Support-inductive transfer from ideal-multiple vanishing

Reverse a generic comparison from an ideal power of the given witness.
The two error sheaves have smaller support, so quotient and extension closure
transfer vanishing to the other coefficient. This avoids a false two-out-of-three
claim for positive cohomology, and applies to actual finite direct images.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
open FLT.Mazur.GlobalIdealPower

universe u

namespace FLT.Mazur.FCurve
open CoherentDevissage

/-- Vanishing for ideal multiples of a witness transfers across a generic comparison. -/
theorem eventualTwistVanishing_of_generic_comparison {X : Scheme.{u}} [IsNoetherian X]
    {L M N : X.Modules} (hL : LocallyFreeRankOne L)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (a : M ⟶ N) (x : X) [IsIso ((stalk x).map a)] (Z : Set X) (hx : x ∈ Z)
    (hM : support M ⊆ Z) (hN : support N ⊆ Z)
    (hsmall : ∀ F : X.Modules, F.IsFinitePresentation → support F ⊂ Z →
      EventualTwistVanishing L F)
    (hideal : ∀ I : X.IdealSheafData, EventualTwistVanishing L (multiple I N)) :
    EventualTwistVanishing L M := by
  obtain ⟨I, n, _, b, _, hk, hc⟩ :=
    IdealPowerGenericComparison.exists_reverse_supported a x Z hx hM hN
  exact EventualTwistVanishing.of_errors hL b (hideal (I ^ n))
    (hsmall _ (coherent_kernel b) hk) (hsmall _ (coherent_cokernel b) hc)

/-- Finite direct images provide the ideal-multiple hypothesis from an ample pullback. -/
theorem finitePushforward_generic_comparison_vanishing
    {R : Type} [CommRing R] [IsNoetherianRing R] {X Y : Scheme}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (g : Y ⟶ X) [IsFinite g]
    {L M : X.Modules} (hL : LocallyFreeRankOne L)
    (hample : AmpleLineBundle ((Scheme.Modules.pullback g).obj L))
    (N : Y.Modules) [N.IsFinitePresentation] [M.IsFinitePresentation]
    (a : M ⟶ (pushforward g).obj N) (x : X) [IsIso ((stalk x).map a)]
    (Z : Set X) (hx : x ∈ Z) (hM : support M ⊆ Z)
    (hN : support ((pushforward g).obj N) ⊆ Z)
    (hsmall : ∀ F : X.Modules, F.IsFinitePresentation → support F ⊂ Z →
      EventualTwistVanishing L F) : EventualTwistVanishing L M := by
  have := Chow.source_isNoetherian f
  have := finitePushforward_isFinitePresentation g N
  exact eventualTwistVanishing_of_generic_comparison hL a x Z hx hM hN hsmall
    (fun I ↦ finitePushforward_ideal_ample_coherent_vanishing f g hL hample N I)

end FLT.Mazur.FCurve
