/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedLabelTransport

/-!
# Transporting actual affine source charts between distinguished labels

Pullback by the label isomorphism preserves affine stable source opens, their
moving actions, and containment over any original invariant coefficient domain.
This transports source charts themselves, without restricting relation arrows.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o o' : I)

instance labelChange_isIso : IsIso (labelChange e I o o') := (labelIso e I o o').isIso_hom

variable (U : (source p q I o').Opens)
  (hU : ∀ σ : Equiv.Perm I, (action e I o' σ).hom ⁻¹ᵁ U = U)

include hU in
/-- The actual inverse image chart is stable under every normalized moving permutation. -/
theorem label_preimage_stable (σ : Equiv.Perm I) :
    (action e I o σ).hom ⁻¹ᵁ (labelChange e I o o' ⁻¹ᵁ U) =
      labelChange e I o o' ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, ← labelChange_action, Scheme.Hom.comp_preimage, hU]

/-- Affine source charts remain affine under any distinguished-label change. -/
theorem label_preimage_affine (ha : IsAffineOpen U) :
    IsAffineOpen (labelChange e I o o' ⁻¹ᵁ U) := ha.preimage_of_isIso _

/-- The transported source chart is isomorphic to the whole original chart. -/
def labelChartIso : (labelChange e I o o' ⁻¹ᵁ U).toScheme ≅ U.toScheme :=
  asIso (labelChange e I o o' ∣_ U)

/-- The chart identification retains the underlying label-change morphism. -/
@[reassoc] theorem labelChartIso_inclusion :
    (labelChartIso e I o o' U).hom ≫ U.ι =
      (labelChange e I o o' ⁻¹ᵁ U).ι ≫ labelChange e I o o' := morphismRestrict_ι _ _

/-- The finite moving actions agree on the transported charts as scheme morphisms. -/
@[reassoc] theorem labelChartIso_equivariant (σ : Equiv.Perm I) :
    (restrictedAction (action e I o) (labelChange e I o o' ⁻¹ᵁ U)
      (label_preimage_stable e I o o' U hU) σ).hom ≫ (labelChartIso e I o o' U).hom =
        (labelChartIso e I o o' U).hom ≫ (restrictedAction (action e I o') U hU σ).hom := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, labelChartIso_inclusion, restrictedAction_hom_ι,
    restrictedAction_hom_ι_assoc, labelChartIso_inclusion_assoc]
  rw [labelChange_action]

variable (W : A.Opens) (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W)

include hW in
/-- Original invariant domains are unchanged when the first endpoint moves to a new label. -/
theorem labelChange_original_domain :
    labelChange e I o o' ⁻¹ᵁ (first p q I o' ⁻¹ᵁ W) = first p q I o ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, labelChange_first, Scheme.Hom.comp_preimage, ← hW,
    ← Scheme.Hom.comp_preimage, coordinate_first]

include hW in
/-- A chart over a prescribed original domain stays over that domain after label transport. -/
theorem label_preimage_domain (hUW : U ≤ first p q I o' ⁻¹ᵁ W) :
    labelChange e I o o' ⁻¹ᵁ U ≤ first p q I o ⁻¹ᵁ W := by
  rw [← labelChange_original_domain e I o o' W hW]
  intro x hx
  exact hUW hx

end FLT.Mazur.EquivalenceRelationNormalizedFrames
