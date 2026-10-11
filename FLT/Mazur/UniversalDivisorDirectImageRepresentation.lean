/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalDivisorAcyclicRankOne
public import FLT.Mazur.ProperAcyclicDirectImageRepresentation

/-!
# The universal-divisor open represents actual acyclic direct-image lines

Apply global open-cover descent to the varying universal-divisor bundle.
The criterion is the actual direct-image line on arbitrary test schemes,
with no Noetherianity or reducedness condition on those tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProperUniversalDirectImage
open FCurve LineSectionBaseChange LocallyFreeDualProjectiveAtlas
attribute [local irreducible] ModuleSheafTensor.tensor
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
  LocallyFreeDualProjectiveAtlas.projection
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "π" => projection M hM
local notation "q" => Limits.pullback.snd f π
variable (K : X.Modules) (hK : LocallyFreeRankOne K)


/-- The original parameter open represents acyclicity and its actual direct-image line. -/
theorem divisorAcyclicRankOneOpen_directImage_represents {P T : Scheme.{0}}
    {a : P ⟶ Limits.pullback f π} {b : P ⟶ T} {g : T ⟶ space M hM}
    (h : IsPullback a b q g) :
    ((∀ t : T, ∀ n, Subsingleton (ModuleH ((pullback (b.fiberι t)).obj
      ((pullback a).obj (divisorTwistedLine f L hL hV K))) (n + 1))) ∧
        LocallyFreeRankOne ((pushforward b).obj
          ((pullback a).obj (divisorTwistedLine f L hL hV K)))) ↔
      ∃! u : T ⟶ (divisorAcyclicRankOneOpen f L hL hV K hK).toScheme,
        u ≫ (divisorAcyclicRankOneOpen f L hL hV K hK).ι = g := by
  let _ := atlas_locallyNoetherian f L hL hV
  exact properLineAcyclicRankOneOpen_directImage_represents q
    (divisorTwistedLine f L hL hV K) (divisorTwistedLine_rankOne f L hL hV K hK) h

/-- The actual universal family's direct image is a line on the constructed simultaneous open. -/
theorem divisorAcyclicRankOneOpen_directImage_rankOne :
    LocallyFreeRankOne
      ((pushforward (q ∣_ divisorAcyclicRankOneOpen f L hL hV K hK)).obj
        ((pullback (q ⁻¹ᵁ divisorAcyclicRankOneOpen f L hL hV K hK).ι).obj
          (divisorTwistedLine f L hL hV K))) := by
  let _ := atlas_locallyNoetherian f L hL hV
  exact properLineAcyclicRankOneOpen_directImage_rankOne q
    (divisorTwistedLine f L hL hV K) (divisorTwistedLine_rankOne f L hL hV K hK)

end FLT.Mazur.ProperUniversalDirectImage
