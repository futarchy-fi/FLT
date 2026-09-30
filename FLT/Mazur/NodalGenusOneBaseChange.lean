/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodalGeometricFiberGenus

/-!
# Base change of necessary genus-one geometric fiber conditions

Pasting a geometric fiber square with the base-change square leaves its structure
map unchanged, preserving the nodal core, constant sections and genus one.
This transports the necessary fiber predicate of DR II Definition 1.4; it does
not construct a generalized elliptic curve or require a cohomology comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.FCurve.CurveFiberHypotheses

/-- Necessary genus-one geometric fiber conditions persist under arbitrary base change. -/
theorem NodalGenusOneGeometricFibers.baseChange
    {X S T : Scheme} {f : X ⟶ S} [IsProper f]
    (h : NodalGenusOneGeometricFibers f) (g : T ⟶ S) :
    NodalGenusOneGeometricFibers (pullback.snd f g) := by
  refine ⟨fun L _ _ s Y fst snd hs ↦ ?_⟩
  exact h.fiber L (s ≫ g) (fst ≫ pullback.fst f g) snd
    (hs.paste_horiz (.of_hasPullback f g))

end FLT.Mazur.FCurve.CurveFiberHypotheses
