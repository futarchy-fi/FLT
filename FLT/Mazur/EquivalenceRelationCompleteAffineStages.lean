/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteStageCoefficients
public import FLT.Mazur.EquivalenceRelationCompleteBoundaryCorrections

/-!
# Constructed complete affine stages on stable original charts

Intersect each actual ideal-power thickening with a stable affine open of the
original normalized source. These complete nonreduced affine sources carry the
moving action and support exact original boundary-kernel corrections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U) (k : ℕ)

/-- The actual inverse-image open in the complete thickening. -/
abbrev completeAffineStageOpen : (completeThickening (p := p) (q := q) I o k).Opens :=
  completeThickeningInclusion I o k ⁻¹ᵁ U

/-- Retain the full original normalized source map on this affine stage. -/
def completeAffineStageInclusion : (completeAffineStageOpen I o U k).toScheme ⟶
    source p q I o := (completeAffineStageOpen I o U k).ι ≫ completeThickeningInclusion I o k

instance completeAffineStageInclusion_mono : Mono (completeAffineStageInclusion I o U k) :=
  inferInstanceAs (Mono ((completeAffineStageOpen I o U k).ι ≫ completeThickeningInclusion I o k))

/-- A stable original open gives a genuine moving action on the complete affine stage. -/
def completeAffineStageAction : Equiv.Perm I →* Aut (completeAffineStageOpen I o U k).toScheme :=
  boundaryOpenAction (completeThickeningAction e I o k) (action e I o)
    (completeThickeningInclusion I o k) (completeThickeningActionMap_inclusion e I o k) U hU

/-- The actual composite source inclusion is equivariant. -/
@[reassoc] theorem completeAffineStageAction_inclusion (σ : Equiv.Perm I) :
    (completeAffineStageAction e I o U hU k σ).hom ≫ completeAffineStageInclusion I o U k =
      completeAffineStageInclusion I o U k ≫ (action e I o σ).hom := by
  change (restrictedAction _ _ _ σ).hom ≫ _ ≫ _ = _
  rw [restrictedAction_hom_ι_assoc]
  exact congrArg (fun f ↦ (completeAffineStageOpen I o U k).ι ≫ f)
    (completeThickeningActionMap_inclusion e I o k σ)

omit e hU in
/-- Every affine stage has full complete support, even at noninterior original points. -/
theorem completeAffineStage_complete :
    Set.range (completeAffineStageInclusion I o U k) ⊆
      completePointLocus (p := p) (q := q) I o := by
  rintro _ ⟨x, rfl⟩
  exact (completeThickeningInclusion_range I o k).le
    ⟨(completeAffineStageOpen I o U k).ι x, rfl⟩

omit e hU in
/-- Affineness uses the closed power quotient over the original affine chart. -/
theorem completeAffineStage_isAffine (ha : IsAffineOpen U) :
    IsAffine (completeAffineStageOpen I o U k).toScheme :=
  ha.preimage (completeThickeningInclusion I o k)

/-- Stage invariants equalize the full original relation on the actual affine-stage source. -/
theorem completeAffineStage_equalizes
    (t : invariantCoordinates (completeAffineStageAction e I o U hU k)) :
    (SourceRestriction.fst (completeAffineStageInclusion I o U k)
      (completeAffineStageInclusion I o U k)).appTop t.val =
    (SourceRestriction.snd (completeAffineStageInclusion I o U k)
      (completeAffineStageInclusion I o U k)).appTop t.val :=
  completeEquivariant_invariant_equalizes e I o (completeAffineStageInclusion I o U k)
    (completeAffineStageAction e I o U hU k) (completeAffineStageAction_inclusion e I o U hU k)
    (completeAffineStage_complete I o U k) t

end FLT.Mazur.EquivalenceRelationNormalizedFrames
