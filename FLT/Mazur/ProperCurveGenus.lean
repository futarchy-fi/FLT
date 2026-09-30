/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveGenus
public import FLT.Mazur.ProperCoherentCohomology

/-!
# Genus of a proper curve

The genus is the dimension of actual first structure-sheaf cohomology. Properness
provides finite-dimensionality. Dimension one and constant global sections remain
explicit hypotheses; neither smoothness nor integrality is required.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))

/-- The genus of a proper curve with constant global sections.
The properness argument supplies finiteness, although `finrank` itself does not use it. -/
@[nolint unusedArguments]
def curveGenus [IsProper f] (_hd : topologicalKrullDim X = 1)
    (_hc : HasConstantGlobalSections f) : ℕ := by
  letI := finiteDimensional_H1_of_proper f
  exact Module.finrank k (H1 f)

/-- Genus is the dimension of first structure-sheaf cohomology. -/
theorem curveGenus_eq_finrank [IsProper f] (hd : topologicalKrullDim X = 1)
    (hc : HasConstantGlobalSections f) :
    curveGenus f hd hc = Module.finrank k (H1 f) := rfl

/-- The genus does not depend on the proofs of the curve hypotheses. -/
theorem curveGenus_proof_independent [IsProper f] (hd hd' : topologicalKrullDim X = 1)
    (hc hc' : HasConstantGlobalSections f) :
    curveGenus f hd hc = curveGenus f hd' hc' := rfl

end FLT.Mazur.FCurve
