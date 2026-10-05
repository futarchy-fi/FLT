/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineBaseAcyclicPower
public import FLT.Mazur.ChowAffineBaseClosedStalk

/-!
# Proper coherent cohomology over a Noetherian ring

Construct finite-cohomology rank-one witnesses by the affine-base Chow
modification. Closed direct image transports them to the original scheme,
and Noetherian coherent dévissage proves finiteness in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage

namespace FLT.Mazur.Chow.AffineBase

variable {R : CommRingCat.{0}} [IsNoetherianRing R] {X : Scheme.{0}} (f : X ⟶ Spec R)
  [IsProper f]

omit [IsNoetherianRing R] [IsProper f] in
/-- The scalar map for a composite is the composite scalar map. -/
lemma baseCohomologyScalars_comp {Y : Scheme.{0}} (g : Y ⟶ X) :
    baseCohomologyScalars (g ≫ f) = g.appTop.hom.comp (baseCohomologyScalars f) := rfl

/-- Properness constructs finite-cohomology witnesses on every integral closed subscheme. -/
theorem proper_hasGenericRankOneRingWitnesses :
    HasGenericRankOneWitnesses (HasFiniteRingCohomology (baseCohomologyScalars f)) := by
  let := Chow.source_isNoetherian f
  let : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from f]; infer_instance⟩
  intro J hJ
  let := hJ
  obtain ⟨n, _, _, hn⟩ := exists_chow_power_ring_finite (J.subschemeι ≫ f)
  let := chowPushforwardPower_isFinitePresentation (J.subschemeι ≫ f) n
  refine ⟨{
    sheaf := closedGraphPower f J n
    finite := closedGraphPower_isFinitePresentation f J n
    support_eq := closedGraphPower_support f J n
    annihilated := closedGraphPower_stalkAnnihilated f J n
    rank_one := closedGraphPower_finrank f J n
    property := ?_ }⟩
  exact (closedPushforward_hasFiniteRingCohomology_iff J.subschemeι
    (graphPowerPushforward (J.subschemeι ≫ f) n) (baseCohomologyScalars f)).mpr hn

/-- Every coherent coefficient on a proper scheme has finite cohomology over its
Noetherian affine base. No projectivity or flatness of the original family is assumed. -/
theorem proper_coherent_hasFiniteRingCohomology (M : X.Modules) [M.IsFinitePresentation] :
    HasFiniteRingCohomology (baseCohomologyScalars f) M := by
  let := Chow.source_isNoetherian f
  exact coherent_hasFiniteRingCohomology_of_witnesses (baseCohomologyScalars f)
    (proper_hasGenericRankOneRingWitnesses f) M

end FLT.Mazur.Chow.AffineBase
