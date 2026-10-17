/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteThickenings
public import FLT.Mazur.GlobalIdealPowerCompatibility

/-!
# The moving action preserves the full complete-locus ideal powers

The action on the original normalized source preserves the actual vanishing
ideal and all its powers. These equalities retain the infinitesimal structure,
not only the closed support, and hold without an affine-source hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- The actual complete support is preserved as an image as well as a preimage. -/
theorem completePointLocus_action_image (σ : Equiv.Perm I) :
    (action e I o σ).hom '' completePointLocus (p := p) (q := q) I o =
      completePointLocus (p := p) (q := q) I o := by
  calc
    _ = (action e I o σ).hom ''
        ((action e I o σ).hom ⁻¹' completePointLocus I o) := by
      rw [completePointLocus_action_invariant]
    _ = _ := Set.image_preimage_eq _ (action e I o σ).hom.surjective

/-- Pushforward along a moving permutation preserves the original vanishing ideal. -/
theorem completeSupportIdeal_map_action (σ : Equiv.Perm I) :
    (completeSupportIdeal (p := p) (q := q) I o).map (action e I o σ).hom =
      completeSupportIdeal (p := p) (q := q) I o := by
  rw [completeSupportIdeal, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  change closure ((action e I o σ).hom '' completePointLocus I o) = _
  rw [completePointLocus_action_image, (completePointLocus_isClosed I o).closure_eq]
  rfl

/-- Pullback preserves the same full ideal, not merely its radical support. -/
theorem completeSupportIdeal_comap_action (σ : Equiv.Perm I) :
    (completeSupportIdeal (p := p) (q := q) I o).comap (action e I o σ).hom =
      completeSupportIdeal (p := p) (q := q) I o := by
  have h (τ : Equiv.Perm I) :
      (completeSupportIdeal (p := p) (q := q) I o).comap (action e I o τ).hom ≤
        completeSupportIdeal (p := p) (q := q) I o := by
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
    exact (completeSupportIdeal_map_action e I o τ).ge
  apply le_antisymm (h σ)
  have h' := Scheme.IdealSheafData.comap_mono (action e I o σ).hom (h σ⁻¹)
  dsimp only at h'
  rw [← Scheme.IdealSheafData.comap_comp] at h'
  change (completeSupportIdeal I o).comap
    (actionMap e I o σ ≫ actionMap e I o σ⁻¹) ≤ _ at h'
  simpa only [← actionMap_mul, inv_mul_cancel, actionMap_one,
    Scheme.IdealSheafData.comap_id] using h'

/-- Every positive or zero ideal power is preserved scheme-theoretically. -/
theorem completeSupportIdeal_pow_comap_action (σ : Equiv.Perm I) (n : ℕ) :
    (completeSupportIdeal (p := p) (q := q) I o ^ n).comap (action e I o σ).hom =
      completeSupportIdeal (p := p) (q := q) I o ^ n := by
  rw [GlobalIdealPowerCompatibility.comap_pow, completeSupportIdeal_comap_action]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
