/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveNode
public import FLT.Mazur.FamilyTransport

/-!
# Necessary nodal fiber hypotheses

This file supplies the nonempty, connected, reduced, pure-dimension-one and nodal
part of the fiber conditions in `docs/DR_SOURCE_LEDGER.md`. Purity is tested on
each irreducible component, not by the dimension of the whole space.

These conditions do not define a DR stable genus-one curve: even after imposing
genus one, an elliptic curve with a rational tail is a counterexample. The extra
trivial-dualizing-sheaf condition, or an actual Néron-polygon classification, remains
to be constructed. Neither is replaced here by an arbitrary proposition.

Geometric fibers are tested over every algebraically closed field in the universe
of the schemes. We quantify over pullback squares, so the condition is independent
of a chosen pullback object and base change follows by pasting squares. In particular
the canonical fiber `pullback f s` is covered. Connectedness here is connectedness
of these geometric fibers; no irreducibility or integrality condition is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve.CurveFiberHypotheses

/-- Every irreducible component, with its subspace topology, has dimension one. -/
def PureDimensionOne (X : Scheme.{u}) : Prop :=
  ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = 1

variable {K : Type u} [Field K] {X S T : Scheme.{u}}

/-- The necessary nodal conditions for a single fiber, without genus or dualizing data. -/
structure NodalFiberCore (f : X ⟶ Spec (CommRingCat.of K)) : Prop where
  finitePresentation : LocallyOfFinitePresentation f
  nonempty : Nonempty X
  connected : ConnectedSpace X
  reduced : IsReduced X
  pureDimension : PureDimensionOne X
  nodes : @CurveNode.AtWorstNodes K _ X f finitePresentation

/-- Necessary geometric fiber conditions, tested on every geometric-point pullback square.
This is a partial contract, not the DR stable-genus-one condition. -/
structure NodalGeometricFibers (f : X ⟶ S) : Prop where
  fiber : ∀ (L : Type u) [Field L] [IsAlgClosed L]
    (s : Spec (CommRingCat.of L) ⟶ S) {Y : Scheme.{u}}
    (fst : Y ⟶ X) (snd : Y ⟶ Spec (CommRingCat.of L)),
    IsPullback fst snd f s → NodalFiberCore snd

/-- The necessary nodal conditions on the canonical geometric fiber. -/
theorem NodalGeometricFibers.pullback {f : X ⟶ S} (h : NodalGeometricFibers f)
    [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) :
    NodalFiberCore (pullback.snd f s) :=
  h.fiber K s _ _ (.of_hasPullback f s)

/-- Necessary geometric fiber conditions persist under every base change. -/
theorem NodalGeometricFibers.baseChange {f : X ⟶ S} (h : NodalGeometricFibers f)
    (g : T ⟶ S) : NodalGeometricFibers (pullback.snd f g) := by
  refine ⟨fun L _ _ s Y fst snd hs ↦ ?_⟩
  exact h.fiber L (s ≫ g) (fst ≫ pullback.fst f g) snd
    (hs.paste_horiz (.of_hasPullback f g))

/-- The existing proper-flat family core together with the necessary nodal fiber core.
Trivial dualizing sheaves and genus remain separate obligations. -/
structure NodalFamilyCore (f : X ⟶ S) : Prop where
  family : ProperFlatFamily f
  fibers : NodalGeometricFibers f

/-- The partial family contract is stable under arbitrary base change, hence also
under base change along geometric points. -/
theorem NodalFamilyCore.baseChange {f : X ⟶ S} (h : NodalFamilyCore f)
    (g : T ⟶ S) : NodalFamilyCore (pullback.snd f g) :=
  ⟨properFlatBaseChange f g h.family, h.fibers.baseChange g⟩

/-- The node part holds for smooth fibers; properness, geometric connectedness and
dimension one are not needed for this implication. -/
theorem nodes_of_smoothFiber (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] :
    CurveNode.AtWorstNodes f :=
  CurveNode.atWorstNodes_of_smooth f

/-- Every fiber over a field of a smooth morphism satisfies the node part. -/
theorem nodes_of_smoothFamily (f : X ⟶ S) [Smooth f]
    (s : Spec (CommRingCat.of K) ⟶ S) :
    CurveNode.AtWorstNodes (pullback.snd f s) :=
  nodes_of_smoothFiber (pullback.snd f s)

end FLT.Mazur.FCurve.CurveFiberHypotheses
