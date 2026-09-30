/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessAffineCoherence
public import FLT.Mazur.CoherentOpenDescent

/-!
# Coherence of Chow witness powers

The actual direct image of every natural tensor power of the Chow line bundle
is coherent. Its affine restrictions are coherent by localization and projective
cohomology finiteness, and finite presentation descends along the affine cover.
The coefficient's finite presentation used there is already proved from its
local rank-one trivializations by `graphLineBundlePower_isFinitePresentation`.
No higher-direct-image acyclicity or Serre vanishing is required.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Scheme.Modules FLT.Mazur.FCurve

namespace FLT.Mazur.Chow

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Every actual Chow witness power has coherent direct image, including power zero. -/
theorem chowPushforwardPower_isFinitePresentation (n : ℕ) :
    (graphPowerPushforward f n).IsFinitePresentation :=
  coherent_of_openCover (graphPowerPushforward f n)
    (fun V : X.affineOpens ↦ V.1) (iSup_affineOpens_eq_top X)
    (graphPowerAffineRestriction_isFinitePresentation f n)

end FLT.Mazur.Chow
