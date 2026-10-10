/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryProperNormalization
public import FLT.Mazur.WeierstrassVariableChangeGroup

/-!
# Canonical auxiliary normalization preserves the actual group scheme

The proper normalization is promoted using its proved global multiplication
compatibility. The resulting group isomorphism retains the original proper
map, its inverse, and every marked section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The original smooth auxiliary cubic with its already constructed group operations. -/
def auxiliaryPullbackGroup : CommGrp (Over (Spec (.of R))) :=
  integralCurveGroup (auxiliaryPullbackEquation g) (auxiliaryPullbackEquation_discriminant g)

/-- The normalized smooth cubic with its already constructed group operations. -/
def auxiliaryNormalizedGroup : CommGrp (Over (Spec (.of R))) :=
  integralCurveGroup (auxiliaryNormalizedEquation g) (auxiliaryNormalizedEquation_discriminant g)

/-- Proper normalization is an actual isomorphism of the original commutative group schemes. -/
def auxiliaryNormalizationGroupIso : auxiliaryNormalizedGroup g ≅ auxiliaryPullbackGroup g :=
  integralVariableChangeGroupIso _ _ (auxiliaryFrameChange g) rfl
    (auxiliaryPullbackEquation_discriminant g) (auxiliaryNormalizedEquation_discriminant g)

/-- The group isomorphism retains the exact proper normalization morphism. -/
theorem auxiliaryNormalizationGroupIso_hom :
    (auxiliaryNormalizationGroupIso g).hom.hom.hom.hom.left =
      (auxiliaryProperNormalization g).hom := rfl

/-- Its inverse retains the exact inverse of the proper normalization morphism. -/
theorem auxiliaryNormalizationGroupIso_inv :
    (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom.left =
      (auxiliaryProperNormalization g).inv := rfl

/-- The group normalization inverse carries each original section to its normalized section. -/
@[reassoc] theorem auxiliaryPullbackSection_normalize (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryPullbackSection g a ha ≫
        (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom.left =
      auxiliaryNormalizedSection g a ha := by
  rw [auxiliaryNormalizationGroupIso_inv, ← auxiliaryNormalizedSection_original]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.UniversalWeierstrass
