/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomRelabelNormalization
public import FLT.Mazur.OddWeierstrassCyclicHomSliceFunctor

/-!
# Relabeling absorption on the full odd normalized slice

The arbitrary-source absorption theorem gives the exact equation of
normalization morphisms, retaining all cyclic labels and collisions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual normalization morphism retains each full normalized parameter. -/
@[reassoc] theorem cyclicHomNormalizationMorphism_parameter {T : Scheme}
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    f ≫ cyclicHomNormalizationMorphism n ≫ cyclicHomNormalizedSliceInclusion n =
      cyclicHomNormalizedPoint n f := by
  rw [← Category.assoc, cyclicHomNormalizationMorphism_comp,
    cyclicHomNormalizedSlicePoint_inclusion]

/-- Full normalization absorbs an intermediate normalization before relabeling. -/
theorem cyclicHomNormalizationMorphism_relabel
    (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) :
    cyclicHomNormalizationMorphism n ≫ cyclicHomNormalizedSliceInclusion n ≫
        (cyclicHomRelabel n a c).left ≫ cyclicHomNormalizationMorphism n =
      (cyclicHomRelabel n a c).left ≫ cyclicHomNormalizationMorphism n := by
  apply (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
  simp only [Category.assoc]
  rw [← Category.assoc (cyclicHomNormalizationMorphism n),
    ← Category.assoc (cyclicHomNormalizationMorphism n ≫ cyclicHomNormalizedSliceInclusion n),
    cyclicHomNormalizationMorphism_parameter, cyclicHomNormalizationMorphism_parameter]
  have hp := cyclicHomNormalizationMorphism_parameter n
    (𝟙 (cyclicHomAuxiliaryScheme n).left)
  simp only [Category.id_comp] at hp
  rw [hp]
  simpa only [Category.id_comp] using
    cyclicHomNormalizedPoint_relabel_normalize n a c (𝟙 (cyclicHomAuxiliaryScheme n).left)

end FLT.Mazur.OddWeierstrassParameter
