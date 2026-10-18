/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupGroupDetection
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso
public import FLT.Mazur.OddWeierstrassCyclicHomMarkedGroupRigidity
public import FLT.Mazur.OddWeierstrassCyclicHomMarkedSubgroupRelation

/-!
# Uniqueness of the actual odd auxiliary-marked subgroup comparisons

Auxiliary rigidity determines the smooth group map on arbitrary bases.
Smoothness of the original source then determines the full curve map and
subgroup map, including the comparison already constructed by normalization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (hf : cyclicHomMultiplicationEquation n f = 0)
  (hg : cyclicHomMultiplicationEquation n g = 0)

/-- The original independent auxiliary labels determine the entire compatible subgroup map. -/
theorem cyclicHomMarkedSubgroupIso_unique
    (a b : CompatibleIso (cyclicHomSubgroup n f hf) (cyclicHomSubgroup n g hg))
    (ha : ∀ i : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i ≫
      a.curve.hom.group = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i)
    (hb : ∀ i : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i ≫
      b.curve.hom.group = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i) : a = b := by
  let ea : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) :=
    CommGrp.mkIso (groupIso a.curve) (IsMonHom.one_hom a.curve.hom.group)
      (IsMonHom.mul_hom a.curve.hom.group)
  let eb : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) :=
    CommGrp.mkIso (groupIso b.curve) (IsMonHom.one_hom b.curve.hom.group)
      (IsMonHom.mul_hom b.curve.hom.group)
  have he := cyclicHomMarkedGroupIso_unique n f g ea eb ha hb
  let _ : Smooth (cyclicHomSourceCurve n f).curve.hom :=
    SmoothOfRelativeDimension.smooth 1 _
  let _ : IsIso (cyclicHomSourceCurve n f).inclusion :=
    inclusion_isIso_of_smooth (cyclicHomSourceCurve n f)
  apply CompatibleIso.eq_of_group a b
  exact congrArg (fun z ↦ z.hom.hom.hom.hom) he

/-- Every specified marked subgroup comparison is the constructed normalization comparison. -/
theorem cyclicHomMarkedSubgroupIso_eq_normalization
    (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g)
    (a : CompatibleIso (cyclicHomSubgroup n f hf) (cyclicHomSubgroup n g hg))
    (ha : ∀ i : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i ≫
      a.curve.hom.group = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i) :
    a = cyclicHomMarkedRelationSubgroupIso n f g h hf hg :=
  cyclicHomMarkedSubgroupIso_unique n f g hf hg a _ ha
    (cyclicHomMarkedRelationSubgroupIso_auxiliary n f g h hf hg)

end FLT.Mazur.OddWeierstrassParameter
