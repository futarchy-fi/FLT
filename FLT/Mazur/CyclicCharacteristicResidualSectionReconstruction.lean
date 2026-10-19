/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicChartResidualSections
public import FLT.Mazur.CyclicCharacteristicResidualTransitionTests

/-!
# Reconstructing residual regular functions on the opposite chart

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

/-- The affine-line morphism of a residual function respects the entire comparison scheme. -/
theorem residualFunctionMorphism_invariant (s : chartResidualSections n (!b)) :
    productArrowSource n (!b) (!b) ≫ (functionEquiv _).symm s.val =
      productArrowTarget n (!b) (!b) ≫ (functionEquiv _).symm s.val := by
  apply (functionEquiv _).injective
  simp only [functionEquiv_comp, Equiv.apply_symm_apply]
  exact s.property

/-- Reconstruct an actual regular function on the opposite characteristic overlap. -/
def residualSectionReconstruction (s : chartResidualSections n (!b)) :
    Γ((transitionOpen n b).toScheme, ⊤) :=
  functionEquiv _ (residualTransitionDescend n b ((functionEquiv _).symm s.val)
    (residualFunctionMorphism_invariant n b s))

/-- Reconstructed sections recover their prescribed value on each actual transition source. -/
theorem residualSectionReconstruction_fac (s : chartResidualSections n (!b))
    (i : (transitionCover n b).I₀) :
    ((transitionCover n b).f i).appTop (residualSectionReconstruction n b s) =
      (transitionTarget n b i).appTop s.val := by
  unfold residualSectionReconstruction
  rw [← functionEquiv_comp, residualTransitionDescend_fac, functionEquiv_comp,
    Equiv.apply_symm_apply]

/-- Actual fppf pullbacks determine the reconstructed regular function uniquely. -/
theorem residualSectionReconstruction_unique (s : chartResidualSections n (!b))
    (t : Γ((transitionOpen n b).toScheme, ⊤))
    (ht : ∀ i, ((transitionCover n b).f i).appTop t =
      (transitionTarget n b i).appTop s.val) : t = residualSectionReconstruction n b s := by
  apply SchemeFppfFamily.cover_sections_ext (transitionCover n b)
  intro i
  rw [ht, residualSectionReconstruction_fac]

/-- Reconstruction respects the ring structure of the full residual equalizer. -/
def residualSectionReconstructionHom :
    chartResidualSections n (!b) →+* Γ((transitionOpen n b).toScheme, ⊤) where
  toFun := residualSectionReconstruction n b
  map_one' := by
    apply SchemeFppfFamily.cover_sections_ext (transitionCover n b)
    intro i
    simp only [residualSectionReconstruction_fac, OneMemClass.coe_one, map_one]
  map_mul' s t := by
    apply SchemeFppfFamily.cover_sections_ext (transitionCover n b)
    intro i
    simp only [residualSectionReconstruction_fac, Subring.coe_mul, map_mul]
  map_zero' := by
    apply SchemeFppfFamily.cover_sections_ext (transitionCover n b)
    intro i
    simp only [residualSectionReconstruction_fac, ZeroMemClass.coe_zero, map_zero]
  map_add' s t := by
    apply SchemeFppfFamily.cover_sections_ext (transitionCover n b)
    intro i
    simp only [residualSectionReconstruction_fac, Subring.coe_add, map_add]

/-- Reconstruction evaluates correctly on every compatible original-family test. -/
theorem residualSectionReconstruction_on_test (s : chartResidualSections n (!b))
    {T : Scheme} (p : T ⟶ (transitionOpen n b).toScheme)
    (q : T ⟶ normalizedLocus n (!b))
    (h : UnmarkedRelated n b (!b) (p ≫ (transitionOpen n b).ι) q) :
    p.appTop (residualSectionReconstruction n b s) = q.appTop s.val := by
  unfold residualSectionReconstruction
  rw [← functionEquiv_comp, residualTransitionDescend_on_test n b _ _ p q h,
    functionEquiv_comp, Equiv.apply_symm_apply]

/-- The reconstructed function retains all residual comparisons on the opposite overlap. -/
theorem residualSectionReconstruction_invariant (s : chartResidualSections n (!b))
    {T : Scheme} (p q : T ⟶ (transitionOpen n b).toScheme)
    (h : UnmarkedRelated n b b
      (p ≫ (transitionOpen n b).ι) (q ≫ (transitionOpen n b).ι)) :
    p.appTop (residualSectionReconstruction n b s) =
      q.appTop (residualSectionReconstruction n b s) := by
  unfold residualSectionReconstruction
  rw [← functionEquiv_comp, ← functionEquiv_comp,
    residualTransitionDescend_invariant n b _ _ p q h]

end FLT.Mazur.CyclicCharacteristicOrbit
