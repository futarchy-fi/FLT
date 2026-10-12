/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationMap

/-!
# Every original label through the global full normalization map

The natural full family retains explicit relative maps into the original and
normalized group families. The actual normalization comparison identifies
these maps, and both projections recover their full universal parameters.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)
local notation "aO" => cyclicSchemeAuxiliaryPoint n (𝟙 _)
local notation "aN" => auxiliarySchemeNormalizedPoint aO

/-- Every original relative label projects to exactly the given full parameter. -/
@[reassoc] theorem cyclicNaturalOriginalMarking_projection (c : CyclicLabels n) :
    f ≫ (cyclicSchemeOriginalMarking n (𝟙 _) c).left ≫
      pullback.fst universalGroup.hom (aO ≫ levelFour.hom) =
        f ≫ (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left := by
  rw [cyclicSchemeOriginalMarking_fst, Category.id_comp]

/-- Every normalized relative label projects to the actual natural full parameter. -/
@[reassoc] theorem cyclicNaturalNormalizedMarking_projection (c : CyclicLabels n) :
    f ≫ (cyclicSchemeNormalizedMarking n (𝟙 _) c).left ≫
      pullback.fst universalGroup.hom (aN ≫ levelFour.hom) =
        (f ≫ cyclicNormalizationMap n) ≫
          (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left := by
  rw [cyclicSchemeNormalizedMarking_fst, Category.assoc]
  rfl

/-- The actual normalization comparison retains every original relative label on every source. -/
@[reassoc] theorem cyclicNaturalNormalizedMarking_compare (c : CyclicLabels n) :
    f ≫ (cyclicSchemeNormalizedMarking n (𝟙 _) c).left ≫
      (auxiliarySchemeNormalizationGroupIso aO).hom.hom.hom.hom.left =
        f ≫ (cyclicSchemeOriginalMarking n (𝟙 _) c).left := by
  have h := congrArg Over.Hom.left (cyclicSchemeNormalizedMarking_compare n (𝟙 _) c)
  exact congrArg (fun k ↦ f ≫ k) h

/-- Natural full slice parameters retain the complete normalized relative marking. -/
@[reassoc] theorem cyclicNaturalNormalizedSlicePoint_value (c : CyclicLabels n) :
    cyclicNaturalNormalizedSlicePoint n f ≫ cyclicNormalizedSliceInclusion n ≫
      (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left =
        f ≫ (cyclicSchemeNormalizedMarking n (𝟙 _) c).left ≫
          pullback.fst universalGroup.hom (aN ≫ levelFour.hom) := by
  rw [← Category.assoc, cyclicNaturalNormalizedSlicePoint_inclusion]
  exact (cyclicNaturalNormalizedMarking_projection n f c).symm

/-- Both the original and normalized relative sections lie over the unchanged source map. -/
@[reassoc] theorem cyclicNaturalNormalizedMarking_base (c : CyclicLabels n) :
    f ≫ (cyclicSchemeNormalizedMarking n (𝟙 _) c).left ≫
      (auxiliarySchemeGroup aN).X.hom = f := by
  rw [(cyclicSchemeNormalizedMarking n (𝟙 _) c).w]
  exact Category.comp_id _

end FLT.Mazur.UniversalWeierstrass
