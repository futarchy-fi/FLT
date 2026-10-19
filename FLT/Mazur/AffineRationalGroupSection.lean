/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRationalGroupSection

/-!
# Affine points as sections of their actual elliptic curve

The comparison retains every point and its addition, so a geometric kernel
can be embedded into the scheme without selecting a new unrelated subgroup.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- The original affine point group embedded into actual sections of its cubic. -/
def affineRationalGroupSectionAddHom : W.toAffine.Point →+
    Additive (𝟙_ (Over (Spec (.of K))) ⟶
      (integralGeneralizedEllipticCurve W W.isUnit_Δ).group) :=
  (projectiveRationalGroupSectionAddHom W W.isUnit_Δ).comp
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.map (algebraMap K K)).toProjective).symm.toAddMonoidHom

/-- Distinct original affine points remain distinct actual sections. -/
theorem affineRationalGroupSectionAddHom_injective :
    Function.Injective (affineRationalGroupSectionAddHom W) :=
  (projectiveRationalGroupSection_injective W W.isUnit_Δ).comp
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      (W.map (algebraMap K K)).toProjective).symm.injective

/-- The comparison preserves the exact order of the specified affine point. -/
theorem affineRationalGroupSectionAddHom_order (P : W.toAffine.Point) :
    addOrderOf (affineRationalGroupSectionAddHom W P) = addOrderOf P :=
  addOrderOf_injective _ (affineRationalGroupSectionAddHom_injective W) P

end FLT.Mazur.WeierstrassIntegralChart
