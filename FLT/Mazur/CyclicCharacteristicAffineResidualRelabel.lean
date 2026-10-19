/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualTests

/-!
# Full affine residual invariants retain the finite relabeling action

Restrict the original compatible relabelings to the actual affine chart. Every
full residual invariant is fixed by these automorphisms, as a regular function
and not merely at underlying points. The converse is not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Full residual invariance implies invariance under each actual affine relabeling. -/
theorem affineResidual_morphism_relabel {Y : Scheme} (f : invariantAffineChart n i ⟶ Y)
    (hf : affineResidualSource n i ≫ f = affineResidualTarget n i ≫ f)
    (g : RelabelGroup n) : (invariantAffineAction n i g).hom ≫ f = f := by
  have h := affineResidual_invariant_on_test n i f hf
    (invariantAffineAction n i g).hom (𝟙 _) (by
      rw [Category.id_comp, invariantAffineAction_inclusion]
      exact unmarkedRelated_relabel n i.1 (invariantAffineInclusion n i) g)
  simpa only [Category.id_comp] using h

/-- The entire full residual spectrum projection respects the affine action. -/
@[reassoc] theorem affineResidualProjection_relabel (g : RelabelGroup n) :
    (invariantAffineAction n i g).hom ≫ affineResidualProjection n i =
      affineResidualProjection n i :=
  affineResidual_morphism_relabel n i _
    (SchemeRelationInvariantSpectrum.projection_condition _ _) g

/-- Every actual residual function is fixed by the original relabeling pullback. -/
theorem affineResidualSections_relabel (s : affineResidualSections n i) (g : RelabelGroup n) :
    (invariantAffineAction n i g).hom.appTop s.val = s.val := by
  let f := (functionEquiv (invariantAffineChart n i)).symm s.val
  have hf : affineResidualSource n i ≫ f = affineResidualTarget n i ≫ f := by
    apply (functionEquiv _).injective
    simp only [functionEquiv_comp, f, Equiv.apply_symm_apply]
    exact s.property
  have h := congrArg (functionEquiv (invariantAffineChart n i))
    (affineResidual_morphism_relabel n i f hf g)
  simpa only [functionEquiv_comp, f, Equiv.apply_symm_apply] using h

/-- The finite fixed functions on the retained original affine source. -/
def affineRelabelSections : Subring Γ(invariantAffineChart n i, ⊤) where
  carrier := {s | ∀ g : RelabelGroup n, (invariantAffineAction n i g).hom.appTop s = s}
  zero_mem' g := map_zero _
  one_mem' g := map_one _
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  mul_mem' ha hb g := by rw [map_mul, ha g, hb g]
  neg_mem' ha g := by rw [map_neg, ha g]

/-- Full residual functions form a subring of the finite fixed functions. -/
theorem affineResidualSections_le_relabel :
    affineResidualSections n i ≤ affineRelabelSections n i :=
  fun s hs g => affineResidualSections_relabel n i ⟨s, hs⟩ g

/-- The inclusion retains the exact original regular function. -/
def affineResidualToRelabel : affineResidualSections n i →+* affineRelabelSections n i :=
  Subring.inclusion (affineResidualSections_le_relabel n i)

/-- Passing to finite fixed functions loses no full residual function. -/
theorem affineResidualToRelabel_injective : Function.Injective (affineResidualToRelabel n i) :=
  fun _ _ h => Subtype.ext
    (congrArg (fun s : affineRelabelSections n i => s.val) h)

end FLT.Mazur.CyclicCharacteristicOrbit
