/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteAdicDiscrepancy
public import FLT.Mazur.SchemeAdicVanishingNeighborhood
public import FLT.Mazur.PolygonDivisorPowerPullback

/-!
# Noetherian separation on the full original normalized relation

The single original discrepancy lies in every power of the pulled-back complete
ideal on every affine relation chart. Separation constructs actual relation
neighborhoods of the full first-endpoint complete support. Source neighborhoods
still require control of relation branches away from this closed support.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
local notation "r" => SourceRestriction.fst U.ι U.ι
local notation "s" => SourceRestriction.snd U.ι U.ι
local notation "R" => SourceRestriction.relation U.ι U.ι

/-- The actual first-endpoint complete ideal on the entire restricted relation. -/
def completeRelationIdeal : (R).IdealSheafData :=
  (completeSupportIdeal (p := p) (q := q) I o).comap ((r) ≫ U.ι)

/-- All nilpotent orders of the fixed original discrepancy survive affine restriction. -/
theorem completeRelation_discrepancy_mem_pow
    (t : invariantCoordinates (restrictedAction (action e I o) U hU))
    (V : (R).affineOpens) (n : ℕ) :
    (R).presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op
      ((r).appTop t.val - (s).appTop t.val) ∈
        (completeRelationIdeal I o U).ideal V ^ (n + 1) := by
  have h := SchemeAdicVanishingNeighborhood.restrict_mem_kernel
    (completeRelationStageInclusion I o U n) _
    (completeRelationStage_discrepancy_zero e I o U hU n t) V
  rw [completeRelationStageInclusion_ker, FCurve.idealSheaf_comap_pow] at h
  exact h

include e in
/-- The actual full restricted relation inherits noetherianity from the original source. -/
theorem completeRelation_locallyNoetherian [IsLocallyNoetherian A] :
    IsLocallyNoetherian R := by
  let _ := first_etale e I o
  let _ := LocallyOfFiniteType.isLocallyNoetherian (first p q I o)
  let _ := relationFirst_etale p q I o e
  let _ := LocallyOfFiniteType.isLocallyNoetherian (relationFirst p q I o)
  have : IsOpenImmersion (original U.ι U.ι) := by
    unfold original
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (original U.ι U.ι)

/-- One relation scalar kills the full discrepancy and is one modulo the complete ideal. -/
theorem completeRelation_affine_annihilator [IsLocallyNoetherian A]
    (t : invariantCoordinates (restrictedAction (action e I o) U hU)) (V : (R).affineOpens) :
    ∃ a : Γ(R, V), 1 - a ∈ (completeRelationIdeal I o U).ideal V ∧
      a * (R).presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op
        ((r).appTop t.val - (s).appTop t.val) = 0 := by
  let _ := completeRelation_locallyNoetherian e I o U
  let _ := IsLocallyNoetherian.component_noetherian V
  exact AdicDiscrepancySeparation.exists_ring_annihilator _ _
    (completeRelation_discrepancy_mem_pow e I o U hU t V)

/-- Actual relation basic opens contain the entire complete support in each affine chart. -/
theorem completeRelation_affine_vanishing_neighborhood [IsLocallyNoetherian A]
    (t : invariantCoordinates (restrictedAction (action e I o) U hU)) (V : (R).affineOpens) :
    ∃ a : Γ(R, V),
      ((completeRelationIdeal I o U).support : Set R) ∩ V.1 ⊆ (R).basicOpen a ∧
      (R).presheaf.map (homOfLE ((R).basicOpen_le a)).op
        ((R).presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op
          ((r).appTop t.val - (s).appTop t.val)) = 0 := by
  let _ := completeRelation_locallyNoetherian e I o U
  obtain ⟨a, _, ha, hz⟩ := SchemeAdicVanishingNeighborhood.exists_affine_neighborhood
    (completeRelationIdeal I o U) V _ (completeRelation_discrepancy_mem_pow e I o U hU t V)
  exact ⟨a, ha, hz⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
