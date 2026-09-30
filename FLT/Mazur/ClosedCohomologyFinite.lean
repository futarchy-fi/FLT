/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPushforwardCohomology
public import FLT.Mazur.CoherentCohomologyFinite

/-!
# Finite cohomology and closed direct image

The existing scalar cohomology comparison transfers all-degree finiteness
between a coherent sheaf on a closed subscheme and its actual direct image.
This is the finiteness transport needed after constructing the Chow witness;
it does not construct that witness or prove its generic rank one.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

variable {k : Type u} [Field k] {X Z : Scheme.{u}}
  [X.IsSeparated] [IsLocallyNoetherian X]

/-- Closed direct image preserves finite cohomology over the specified base field
in both directions. -/
theorem closedPushforward_hasFiniteCohomology_iff
    (j : Z ⟶ X) [IsClosedImmersion j] (f : X ⟶ Spec (CommRingCat.of k))
    (G : Z.Modules) [G.IsFinitePresentation] :
    HasFiniteCohomology f ((pushforward j).obj G) ↔ HasFiniteCohomology (j ≫ f) G := by
  constructor
  · intro h n
    let := h n
    exact Module.Finite.equiv (closedPushforwardScalarHEquiv j G f n)
  · intro h n
    let := h n
    exact Module.Finite.equiv (closedPushforwardScalarHEquiv j G f n).symm

end FLT.Mazur.FCurve
