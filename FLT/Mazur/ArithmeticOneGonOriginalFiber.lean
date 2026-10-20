/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonTorus
public import FLT.Mazur.OneGonRootsOfUnitySubgroup
public import FLT.Mazur.PolygonGeneralizedCurveActionExt

/-!
# The arithmetic boundary cubic retains the original pinched one-gon

The comparison preserves the original smooth inclusion and group coordinate.
Density of the original tori then proves equivariance on the whole curve.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.ArithmeticOneGonOriginalFiber

open OneGonSmoothing ArithmeticOneGonTorus

variable (K : Type) [Field K]
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)

/-- The full original pinching comparison over the original coefficient field. -/
def wholeIso : (E).curve ≅ (boundaryCurve K).curve := zeroFiberOverIso K

/-- The corrected group comparison retains both original torus presentations. -/
def smoothIso : (E).group ≅ (boundaryCurve K).group :=
  (rootsOfUnityTorusIso K).symm ≪≫ torusIso K

instance smoothIso_isMonHom : IsMonHom (smoothIso K).hom := by
  dsimp only [smoothIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The singleton component maps to exactly the corrected arithmetic torus. -/
@[reassoc] theorem smoothIso_component (i : ZMod 1) :
    PolygonSplitGroup.component K 1 i ≫ (smoothIso K).hom = (torusIso K).hom := by
  change PolygonSplitGroup.component K 1 i ≫
    (originalOneGonGroupTorusIso K).hom.hom.hom.hom ≫ _ = _
  rw [originalOneGonGroupTorusIso_component_assoc]

/-- The original whole-curve and smooth-group comparisons preserve the actual inclusion. -/
theorem inclusion :
    (E).inclusion ≫ (wholeIso K).hom =
      (smoothIso K).hom ≫ (boundaryCurve K).inclusion := by
  apply Sigma.hom_ext
  intro i
  simp only [← Category.assoc, smoothIso_component]
  apply Over.OverMorphism.ext
  change (PolygonSplitGroup.component K 1 i ≫ (E).inclusion).left ≫
    (zeroFiberIso K).hom = _
  rw [originalOneGon_inclusion_component, torus_zeroFiberIso_group]
  exact (congrArg Over.Hom.left (torusIso_inclusion K)).symm

/-- The original pinched one-gon is the entire arithmetic boundary generalized curve. -/
def curveIso : (E) ≅ boundaryCurve K :=
  PolygonGeneralizedCurve.isoOfInclusion K 1 Nat.zero_lt_one
    (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)
    (wholeIso K) (smoothIso K) (inclusion K)

/-- The full comparison retains the original global pinching map. -/
theorem curveIso_curve : (curveIso K).hom.curve.left = (zeroFiberIso K).hom := rfl

/-- The full comparison retains the corrected group map. -/
theorem curveIso_group : (curveIso K).hom.group = (smoothIso K).hom := rfl

end FLT.Mazur.ArithmeticOneGonOriginalFiber
