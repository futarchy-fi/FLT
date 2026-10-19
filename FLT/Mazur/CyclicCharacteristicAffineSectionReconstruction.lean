/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualSections
public import FLT.Mazur.CyclicCharacteristicAffineOppositeTests

/-!
# Reconstructing full affine residual functions on the opposite domain

Every function invariant under the full same-chart relation has a unique
regular extension to the opposite characteristic overlap, prescribed on the
actual fppf transition cover. Reconstruction is a ring homomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)
  (j : (invariantAffineCover n (!b)).I₀)

/-- The affine-line morphism of a residual function respects the entire comparison scheme. -/
theorem affineResidualFunctionMorphism_invariant (s : affineResidualSections n ⟨!b, j⟩) :
    affineResidualSource n ⟨!b, j⟩ ≫ (functionEquiv _).symm s.val =
      affineResidualTarget n ⟨!b, j⟩ ≫ (functionEquiv _).symm s.val := by
  apply (functionEquiv _).injective
  simp only [functionEquiv_comp, Equiv.apply_symm_apply]
  exact s.property

/-- Reconstruct an actual regular function on the opposite characteristic overlap. -/
def affineSectionReconstruction (s : affineResidualSections n ⟨!b, j⟩) :
    Γ((affineOppositeOpen n b j).toScheme, ⊤) :=
  functionEquiv _ (affineOppositeDescend n b j ((functionEquiv _).symm s.val)
    (affineResidualFunctionMorphism_invariant n b j s))

/-- Reconstructed sections recover their prescribed value on each actual transition source. -/
theorem affineSectionReconstruction_fac (s : affineResidualSections n ⟨!b, j⟩)
    (i : (affineOppositeCover n b j).I₀) :
    ((affineOppositeCover n b j).f i).appTop (affineSectionReconstruction n b j s) =
      (affineOppositeTarget n b j i).appTop s.val := by
  unfold affineSectionReconstruction
  rw [← functionEquiv_comp, affineOppositeDescend_fac, functionEquiv_comp,
    Equiv.apply_symm_apply]

/-- Actual fppf pullbacks determine the reconstructed regular function uniquely. -/
theorem affineSectionReconstruction_unique (s : affineResidualSections n ⟨!b, j⟩)
    (t : Γ((affineOppositeOpen n b j).toScheme, ⊤))
    (ht : ∀ i, ((affineOppositeCover n b j).f i).appTop t =
      (affineOppositeTarget n b j i).appTop s.val) : t = affineSectionReconstruction n b j s := by
  apply SchemeFppfFamily.cover_sections_ext (affineOppositeCover n b j)
  intro i
  rw [ht, affineSectionReconstruction_fac]

/-- Reconstruction respects the ring structure of the full residual equalizer. -/
def affineSectionReconstructionHom :
    affineResidualSections n ⟨!b, j⟩ →+* Γ((affineOppositeOpen n b j).toScheme, ⊤) where
  toFun := affineSectionReconstruction n b j
  map_one' := by
    apply SchemeFppfFamily.cover_sections_ext (affineOppositeCover n b j)
    intro i
    simp only [affineSectionReconstruction_fac, OneMemClass.coe_one, map_one]
  map_mul' s t := by
    apply SchemeFppfFamily.cover_sections_ext (affineOppositeCover n b j)
    intro i
    simp only [affineSectionReconstruction_fac, Subring.coe_mul, map_mul]
  map_zero' := by
    apply SchemeFppfFamily.cover_sections_ext (affineOppositeCover n b j)
    intro i
    simp only [affineSectionReconstruction_fac, ZeroMemClass.coe_zero, map_zero]
  map_add' s t := by
    apply SchemeFppfFamily.cover_sections_ext (affineOppositeCover n b j)
    intro i
    simp only [affineSectionReconstruction_fac, Subring.coe_add, map_add]

/-- Reconstruction evaluates correctly on every compatible original-family test. -/
theorem affineSectionReconstruction_on_test (s : affineResidualSections n ⟨!b, j⟩)
    {T : Scheme} (p : T ⟶ (affineOppositeOpen n b j).toScheme)
    (q : T ⟶ invariantAffineChart n ⟨!b, j⟩)
    (h : UnmarkedRelated n b (!b) (p ≫ (affineOppositeOpen n b j).ι)
      (q ≫ invariantAffineInclusion n ⟨!b, j⟩)) :
    p.appTop (affineSectionReconstruction n b j s) = q.appTop s.val := by
  unfold affineSectionReconstruction
  rw [← functionEquiv_comp, affineOppositeDescend_on_test n b j _ _ p q h,
    functionEquiv_comp, Equiv.apply_symm_apply]

/-- The reconstructed function retains all residual comparisons on the opposite overlap. -/
theorem affineSectionReconstruction_invariant (s : affineResidualSections n ⟨!b, j⟩)
    {T : Scheme} (p q : T ⟶ (affineOppositeOpen n b j).toScheme)
    (h : UnmarkedRelated n b b
      (p ≫ (affineOppositeOpen n b j).ι) (q ≫ (affineOppositeOpen n b j).ι)) :
    p.appTop (affineSectionReconstruction n b j s) =
      q.appTop (affineSectionReconstruction n b j s) := by
  unfold affineSectionReconstruction
  rw [← functionEquiv_comp, ← functionEquiv_comp,
    affineOppositeDescend_invariant n b j _ _ p q h]

end FLT.Mazur.CyclicCharacteristicOrbit
