/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGeneralizedEllipticModel
public import FLT.Mazur.WeierstrassSmoothGoodReductionGroup

/-!
# The smooth group of the genuine good-reduction generalized model

The comparison uses the existing generalized elliptic curve and the actual
smooth open inclusion. It preserves the constructed operations and the original
identity section, without choosing a replacement model or group law.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The genuine generalized model's group inclusion is the identity of the original cubic. -/
theorem integralGeneralizedEllipticCurve_inclusion :
    (integralGeneralizedEllipticCurve W hΔ).inclusion = 𝟙 (integralCurveOver W) :=
  integralCurveSmoothIso_inclusion W hΔ

/-- Its marked identity is the original projective point at infinity. -/
theorem integralGeneralizedEllipticCurve_identity :
    (integralGeneralizedEllipticCurve W hΔ).identitySection = integralCurveOverZero W := by
  change integralCurveOverZero W ≫
    (integralGeneralizedEllipticCurve W hΔ).inclusion = _
  rw [integralGeneralizedEllipticCurve_inclusion, Category.comp_id]

/-- Bundle the existing generalized model's actual commutative group. -/
def integralGeneralizedGroup : CommGrp (Over (Spec (.of R))) :=
  ⟨(integralGeneralizedEllipticCurve W hΔ).group⟩

/-- The Weierstrass smooth group is the genuine generalized model's existing group. -/
def integralGeneralizedSmoothGroupIso :
    integralSmoothGroup W ≅ integralGeneralizedGroup W hΔ :=
  integralSmoothGoodReductionGroupIso W hΔ

/-- The comparison morphism is the original smooth-open inclusion. -/
theorem integralGeneralizedSmoothGroupIso_hom :
    (integralGeneralizedSmoothGroupIso W hΔ).hom.hom.hom.hom.left =
      (integralSmoothOpen W).ι := rfl

end FLT.Mazur.WeierstrassIntegralChart
