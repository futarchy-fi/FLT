/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteVanishingOpen
public import FLT.Mazur.SchemeUniformAdicVanishing

/-!
# A full relation neighborhood independent of the invariant coefficient

All moving-invariant coefficients equalize on the same open of the full
original relation. Noetherianity and the all-order complete-locus comparison
put every complete first-endpoint fiber in this one open. The neighborhood
is in the relation scheme; a source neighborhood is still a separate task.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction FiniteGroupRestriction SchemeFiniteGroupQuotient
open SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
local notation "r" => SourceRestriction.fst U.ι U.ι
local notation "s" => SourceRestriction.snd U.ι U.ι
local notation "R" => SourceRestriction.relation U.ι U.ι
local notation "C" => invariantCoordinates (restrictedAction (action e I o) U hU)

/-- The common zero-germ open of all moving-invariant full relation discrepancies. -/
def completeUniformRelationVanishingOpen : (R).Opens :=
  uniformVanishingOpen (fun t : C ↦ (r).appTop t.val - (s).appTop t.val)

omit [Etale p] in
/-- Every original moving-invariant coefficient equalizes on this same open. -/
theorem completeUniformRelationVanishingOpen_equalizes (t : C) :
    ((completeUniformRelationVanishingOpen e I o U hU).ι ≫ (r)).appTop t.val =
      ((completeUniformRelationVanishingOpen e I o U hU).ι ≫ (s)).appTop t.val := by
  have h := uniformVanishingOpen_inclusion_zero
    (fun a : C ↦ (r).appTop a.val - (s).appTop a.val) t
  rw [map_sub, sub_eq_zero] at h
  simpa only [completeUniformRelationVanishingOpen, Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply] using h

/-- Every complete first-endpoint arrow lies in the coefficient-independent open. -/
theorem completeUniformRelationVanishingOpen_contains [IsLocallyNoetherian A] :
    ((r) ≫ U.ι) ⁻¹' completePointLocus (p := p) (q := q) I o ⊆
      completeUniformRelationVanishingOpen e I o U hU := by
  let _ := completeRelation_locallyNoetherian e I o U
  rw [← completeRelationIdeal_support]
  exact support_subset_uniformVanishingOpen _ (completeRelationIdeal I o U)
    (fun t ↦ completeRelation_discrepancy_mem_pow e I o U hU t)

/-- Each affine relation chart has one annihilator for all invariant discrepancies. -/
theorem completeRelation_affine_uniform_annihilator [IsLocallyNoetherian A]
    (V : (R).affineOpens) :
    ∃ a : Γ(R, V), 1 - a ∈ (completeRelationIdeal I o U).ideal V ∧
      ∀ t : C, a * (R).presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op
        ((r).appTop t.val - (s).appTop t.val) = 0 := by
  let _ := completeRelation_locallyNoetherian e I o U
  let _ := IsLocallyNoetherian.component_noetherian V
  obtain ⟨a, ha, h⟩ := AdicDiscrepancySeparation.exists_uniform_ring_annihilator
    ((completeRelationIdeal I o U).ideal V)
  exact ⟨a, ha, fun t ↦ h _ (completeRelation_discrepancy_mem_pow e I o U hU t V)⟩

omit [Etale p] in
/-- All tests through the common relation open preserve every invariant coefficient. -/
theorem completeUniformRelationVanishingOpen_test {T : Scheme}
    (g : T ⟶ (completeUniformRelationVanishingOpen e I o U hU).toScheme) (t : C) :
    (g ≫ (completeUniformRelationVanishingOpen e I o U hU).ι ≫ (r)).appTop t.val =
      (g ≫ (completeUniformRelationVanishingOpen e I o U hU).ι ≫ (s)).appTop t.val := by
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
    congrArg (fun x ↦ g.appTop x)
      (completeUniformRelationVanishingOpen_equalizes e I o U hU t)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
