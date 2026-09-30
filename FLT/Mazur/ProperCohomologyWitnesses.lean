/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessClosedStalk
public import FLT.Mazur.ChowWitnessFiniteCohomology
public import FLT.Mazur.ClosedCohomologyFinite
public import FLT.Mazur.CoherentGenericRankOneCriterion

/-!
# Generic-rank-one finite-cohomology witnesses for proper schemes

For each integral closed subscheme, choose an acyclic Chow line power and push
it to the ambient scheme. Coherence, closed support and the canonical generic
residue dimension come from the geometric witness construction. Closed direct
image transports its finite cohomology to the original field structure map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open FLT.Mazur.Chow FLT.Mazur.FCurve.CoherentDevissage

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Properness supplies finite-cohomology witnesses on every integral closed subscheme. -/
theorem proper_hasGenericRankOneWitnesses :
    HasGenericRankOneWitnesses (HasFiniteCohomology f) := by
  let := source_isNoetherian f
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  intro J hJ
  let := hJ
  obtain ⟨n, _, hn⟩ := exists_chow_power_finite (J.subschemeι ≫ f)
  let := chowPushforwardPower_isFinitePresentation (J.subschemeι ≫ f) n
  exact ⟨{
    sheaf := closedGraphPower f J n
    finite := closedGraphPower_isFinitePresentation f J n
    support_eq := closedGraphPower_support f J n
    annihilated := closedGraphPower_stalkAnnihilated f J n
    rank_one := closedGraphPower_finrank f J n
    property := (closedPushforward_hasFiniteCohomology_iff J.subschemeι f
      (graphPowerPushforward (J.subschemeι ≫ f) n)).mpr hn }⟩

end FLT.Mazur.FCurve
