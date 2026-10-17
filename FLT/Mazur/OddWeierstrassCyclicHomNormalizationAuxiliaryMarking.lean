/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationGroup
public import FLT.Mazur.OddWeierstrassCyclicHomRelabelAuxiliary

/-!
# Full cyclic normalization also preserves the independent auxiliary frame

The reconstructed source comparison preserves all auxiliary labels in addition
to every cyclic value. This supplies actual marked-family comparison data.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "a" => cyclicHomAuxiliaryPoint n f
local notation "fN" => cyclicHomNormalizedPoint n f
local notation "aN" => auxiliarySchemeNormalizedPoint a

/-- The reconstructed normalized auxiliary frame agrees under the coefficient comparison. -/
theorem cyclicHomNormalizationBaseIso_auxiliary (c : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fN) c ≫
      (cyclicHomNormalizationBaseIso n f).hom.hom.hom.hom =
        auxiliarySchemeMarking aN c := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc, cyclicHomNormalizationBaseIso_fst,
    auxiliarySchemeMarking_fst]
  exact congrArg (fun z ↦ z ≫ (levelThreeMarking c).left)
    (cyclicHomNormalizedPoint_auxiliary n f)

/-- The full actual normalization preserves every independent auxiliary label. -/
theorem cyclicHomNormalizationGroupIso_auxiliary (c : Labels 3) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n fN) c ≫
      (cyclicHomNormalizationGroupIso n f).hom.hom.hom.hom =
        auxiliarySchemeMarking a c := by
  rw [cyclicHomNormalizationGroupIso_def]
  change _ ≫ (cyclicHomNormalizationBaseIso n f).hom.hom.hom.hom ≫
    (auxiliarySchemeNormalizationGroupIso a).hom.hom.hom.hom = _
  rw [← Category.assoc, cyclicHomNormalizationBaseIso_auxiliary,
    auxiliarySchemeNormalizationGroupIso_marking]

/-- The established full source marking is exactly the actual auxiliary scheme marking. -/
theorem cyclicHomFullAuxiliaryMarking_eq_scheme :
    cyclicHomFullAuxiliaryMarking n f = auxiliarySchemeMarking a := rfl

/-- The same normalization comparison preserves the established full source auxiliary marking. -/
theorem cyclicHomNormalizationGroupIso_fullAuxiliary (c : Labels 3) :
    cyclicHomFullAuxiliaryMarking n fN c ≫
      (cyclicHomNormalizationGroupIso n f).hom.hom.hom.hom =
        cyclicHomFullAuxiliaryMarking n f c :=
  cyclicHomNormalizationGroupIso_auxiliary n f c

end FLT.Mazur.OddWeierstrassParameter
