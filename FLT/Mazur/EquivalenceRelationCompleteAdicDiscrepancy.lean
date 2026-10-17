/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteThickeningTower
public import FLT.Mazur.EquivalenceRelationCompleteEquivariantCoefficients

/-!
# One ambient invariant has zero full discrepancy at every complete ideal power

Only the first source endpoint is restricted to a complete thickening; the
second ranges over the entire original stable open. The discrepancy of the
same ambient coefficient vanishes on every actual power-quotient pullback.
Turning this into an ambient open equality still requires a finite extension
argument; no intersection-of-powers or algebraization assertion is made here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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

/-- Impose the full complete ideal power at the first endpoint of the original relation. -/
def completeRelationStage (k : ℕ) : Scheme :=
  pullback ((r) ≫ U.ι) (completeThickeningInclusion I o k)

/-- The actual closed inclusion into the unchanged full original relation. -/
def completeRelationStageInclusion (k : ℕ) : completeRelationStage I o U k ⟶ R :=
  pullback.fst _ _

instance completeRelationStageInclusion_closed (k : ℕ) :
    IsClosedImmersion (completeRelationStageInclusion I o U k) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst _ (completeThickeningInclusion I o k)))

/-- The stage retains exactly the pulled-back original ideal power, with all nilpotents. -/
theorem completeRelationStageInclusion_ker (k : ℕ) :
    (completeRelationStageInclusion I o U k).ker =
      (completeSupportIdeal (p := p) (q := q) I o ^ (k + 1)).comap ((r) ≫ U.ι) := by
  rw [completeRelationStageInclusion, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  change (Scheme.IdealSheafData.subschemeι _).ker.comap _ = _
  rw [Scheme.IdealSheafData.ker_subschemeι]

/-- Every point on the first-endpoint power quotient has complete first support. -/
theorem completeRelationStage_complete (k : ℕ) :
    Set.range (completeRelationStageInclusion I o U k ≫ original U.ι U.ι ≫
      relationFirst p q I o) ⊆ completePointLocus (p := p) (q := q) I o := by
  rw [original_first, completeRelationStageInclusion, pullback.condition]
  rintro _ ⟨x, rfl⟩
  exact (completeThickeningInclusion_range I o k).le
    ⟨pullback.snd ((r) ≫ U.ι) (completeThickeningInclusion I o k) x, rfl⟩

/-- One ambient invariant satisfies the full mixed equation on every first-endpoint stage. -/
theorem completeRelationStage_invariant_equalizes (k : ℕ)
    (t : invariantCoordinates (restrictedAction (action e I o) U hU)) :
    (completeRelationStageInclusion I o U k ≫ (r)).appTop t.val =
      (completeRelationStageInclusion I o U k ≫ (s)).appTop t.val := by
  apply completeEquivariant_invariant_test_of_support e I o U.ι
    (restrictedAction (action e I o) U hU) (restrictedAction_hom_ι (action e I o) U hU) t
    (completeRelationStageInclusion I o U k ≫ original U.ι U.ι)
  · rw [Category.assoc, Category.assoc, original_first]
  · rw [Category.assoc, Category.assoc, original_second]
  · simpa only [Category.assoc] using completeRelationStage_complete I o U k

/-- The exact full ambient discrepancy lies in every constructed stage restriction kernel. -/
theorem completeRelationStage_discrepancy_zero (k : ℕ)
    (t : invariantCoordinates (restrictedAction (action e I o) U hU)) :
    (completeRelationStageInclusion I o U k).appTop
      ((r).appTop t.val - (s).appTop t.val) = 0 := by
  rw [map_sub]
  change ((r).appTop ≫ (completeRelationStageInclusion I o U k).appTop) t.val -
    ((s).appTop ≫ (completeRelationStageInclusion I o U k).appTop) t.val = 0
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    completeRelationStage_invariant_equalizes e I o U hU k t, sub_self]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
