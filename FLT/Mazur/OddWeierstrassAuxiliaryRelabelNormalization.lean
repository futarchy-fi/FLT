/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryCyclicExtension
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeNormalizationRetraction

/-!
# Actual odd auxiliary normalization absorbs relabeling

Project full cyclic absorption along the constructed trivial extension.
No auxiliary family comparison or normalized-point equality is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Intermediate normalization is absorbed before relabeling on every original source scheme. -/
theorem auxiliarySchemeNormalizedPoint_relabel_normalize {T : Scheme}
    (f : T ⟶ levelThree.left) (e : MulAut (Labels 3)) :
    auxiliarySchemeNormalizedPoint (auxiliarySchemeNormalizedPoint f ≫ (levelThreeAction e).hom) =
      auxiliarySchemeNormalizedPoint (f ≫ (levelThreeAction e).hom) := by
  have h := congrArg (fun z ↦ cyclicHomAuxiliaryPoint 1 z)
    (cyclicHomNormalizedPoint_relabel_normalize 1 e 1 (auxiliaryTrivialCyclicExtension 1 f))
  simpa only [cyclicHomNormalizedPoint_auxiliaryPoint, cyclicHomRelabel_auxiliaryPoint,
    auxiliaryTrivialCyclicExtension_auxiliary] using h

/-- The actual auxiliary closed-slice points obey the same absorption equation. -/
theorem auxiliarySchemeNormalizedSlicePoint_relabel_normalize {T : Scheme}
    (f : T ⟶ levelThree.left) (e : MulAut (Labels 3)) :
    auxiliarySchemeNormalizedSlicePoint
        (auxiliarySchemeNormalizedPoint f ≫ (levelThreeAction e).hom) =
      auxiliarySchemeNormalizedSlicePoint (f ≫ (levelThreeAction e).hom) := by
  apply (cancel_mono normalizedSliceInclusion).mp
  rw [auxiliarySchemeNormalizedSlicePoint_inclusion,
    auxiliarySchemeNormalizedSlicePoint_inclusion,
    auxiliarySchemeNormalizedPoint_relabel_normalize]

/-- The normalization morphism absorbs an intermediate normalization before relabeling. -/
theorem auxiliaryNormalizationMorphism_relabel (e : MulAut (Labels 3)) :
    auxiliaryNormalizationMorphism ≫ normalizedSliceInclusion ≫
        (levelThreeAction e).hom ≫ auxiliaryNormalizationMorphism =
      (levelThreeAction e).hom ≫ auxiliaryNormalizationMorphism := by
  have h := auxiliarySchemeNormalizedSlicePoint_relabel_normalize (𝟙 levelThree.left) e
  rw [← auxiliarySchemeNormalizedSlicePoint_inclusion] at h
  simpa only [← auxiliaryNormalizationMorphism_comp, Category.id_comp, Category.assoc] using h

end FLT.Mazur.OddWeierstrassParameter
