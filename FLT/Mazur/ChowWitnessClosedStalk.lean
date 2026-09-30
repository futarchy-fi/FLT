/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessCoherence
public import FLT.Mazur.ChowWitnessGenericRestriction

/-!
# Closed Chow witness stalks

The actual Chow power on an integral closed subscheme pushes forward to a
coherent sheaf with exactly that closed support. Its generic stalk is killed
by the ambient maximal ideal and has dimension one for the canonical residue
action. These are the geometric fields of the generic-rank-one witness;
no cohomology finiteness or Serre vanishing is assumed here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentGenericCoordinates FLT.Mazur.CoherentGenericIdealEmbedding

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]
  (J : X.IdealSheafData)

/-- The Chow power on the closed subscheme, pushed all the way to the ambient scheme. -/
def closedGraphPower (n : ℕ) : X.Modules :=
  (pushforward J.subschemeι).obj (graphPowerPushforward (J.subschemeι ≫ f) n)

/-- The actual closed Chow witness is coherent for every natural power. -/
theorem closedGraphPower_isFinitePresentation (n : ℕ) :
    (closedGraphPower f J n).IsFinitePresentation := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  let := chowPushforwardPower_isFinitePresentation (J.subschemeι ≫ f) n
  exact closedPushforward_isFinitePresentation J.subschemeι _

variable [IsIntegral J.subscheme]

/-- At the integral generic point, the ambient maximal ideal acts by zero. -/
theorem closedGraphPower_stalkAnnihilated (n : ℕ) :
    StalkAnnihilated (closedGraphPower f J n) (J.subschemeι (genericPoint J.subscheme)) := by
  intro r hr m
  apply (closedStalkAddEquiv J.subschemeι
    (graphPowerPushforward (J.subschemeι ≫ f) n) (genericPoint J.subscheme)).injective
  rw [closedStalk_smul, map_zero]
  have hz : J.subschemeι.stalkMap (genericPoint J.subscheme) r = 0 := by
    change r ∈ RingHom.ker (J.subschemeι.stalkMap (genericPoint J.subscheme)).hom
    rw [← CoherentClosedReduction.stalkIdeal_eq_ker,
      CoherentClosedReduction.generic_stalkIdeal]
    exact hr
  rw [hz, zero_smul]

/-- Closed stalk comparison and the generic field comparison give residue coordinates. -/
def closedGraphPowerResidueCoordinates (n : ℕ) :
    letI := residueModule (closedGraphPower f J n) _
      (closedGraphPower_stalkAnnihilated f J n)
    (closedGraphPower f J n).presheaf.stalk (J.subschemeι (genericPoint J.subscheme)) ≃ₗ[
      X.residueField (J.subschemeι (genericPoint J.subscheme))]
        X.residueField (J.subschemeι (genericPoint J.subscheme)) := by
  letI := residueModule (closedGraphPower f J n) _
    (closedGraphPower_stalkAnnihilated f J n)
  let a := closedStalkAddEquiv J.subschemeι
    (graphPowerPushforward (J.subschemeι ≫ f) n) (genericPoint J.subscheme)
  let b := graphPowerGenericCoordinates (J.subschemeι ≫ f) n
  let q := residueFieldIso J
  refine { toAddEquiv := a.trans (b.toAddEquiv.trans q.symm.toAddEquiv), map_smul' := ?_ }
  intro r m
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective r
  change q.symm (b (a ((X.residue _) s • m))) =
    (X.residue _) s * q.symm (b (a m))
  rw [residue_smul, closedStalk_smul, b.map_smul]
  change q.symm (J.subschemeι.stalkMap _ s * b (a m)) = _
  rw [map_mul, ← residueFieldIso_residue J, RingEquiv.symm_apply_apply]

/-- The residue dimension is one for the action defined by the preceding annihilation proof. -/
theorem closedGraphPower_finrank (n : ℕ) :
    letI := residueModule (closedGraphPower f J n) _
      (closedGraphPower_stalkAnnihilated f J n)
    Module.finrank (X.residueField (J.subschemeι (genericPoint J.subscheme)))
      ((closedGraphPower f J n).presheaf.stalk
        (J.subschemeι (genericPoint J.subscheme))) = 1 := by
  let := residueModule (closedGraphPower f J n) _
    (closedGraphPower_stalkAnnihilated f J n)
  exact (closedGraphPowerResidueCoordinates f J n).finrank_eq.trans (Module.finrank_self _)

/-- Closed coherent support containing the generic point is the whole closed image. -/
theorem closedGraphPower_support (n : ℕ) :
    support (closedGraphPower f J n) = Set.range J.subschemeι := by
  let := closedGraphPower_isFinitePresentation f J n
  apply Set.Subset.antisymm (support_closedPushforward_subset_range J.subschemeι _)
  have hη : J.subschemeι (genericPoint J.subscheme) ∈ support (closedGraphPower f J n) := by
    obtain ⟨m, hm, _, _⟩ := exists_cyclic_generator (closedGraphPower f J n) _
      (closedGraphPower_stalkAnnihilated f J n) (closedGraphPower_finrank f J n)
    intro hz
    exact hm ((AddCommGrpCat.isZero_iff_subsingleton.mp hz).elim m 0)
  have hg : IsGenericPoint (J.subschemeι (genericPoint J.subscheme))
      (Set.range J.subschemeι) := by
    simpa only [Set.image_univ, J.subschemeι.isClosedEmbedding.isClosed_range.closure_eq]
      using (genericPoint_spec J.subscheme).image J.subschemeι.continuous
  exact (hg.mem_closed_set_iff (isClosed_support (closedGraphPower f J n))).mp hη

end FLT.Mazur.Chow
