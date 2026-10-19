/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSmoothPointComparison

/-!
# Original affine points remain distinct on the whole cubic

The projective comparison proves injectivity of the actual morphisms into
the integral curve, over every coefficient field extension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L] (E : WeierstrassCurve K)

/-- The original affine-to-integral scheme comparison is injective. -/
theorem affineSmoothPoint_inclusion_injective :
    Function.Injective (fun P : (E.map (algebraMap K L)).toAffine.Point ↦
      affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) := by
  classical
  intro P Q h
  apply (Projective.Point.toAffineAddEquiv
    (E.map (algebraMap K L)).toProjective).symm.injective
  change Projective.Point.fromAffine P = Projective.Point.fromAffine Q
  apply projectiveToIntegral_injective E
  apply Over.OverMorphism.ext
  simpa only [affineSmoothPoint, projectiveToSmooth_inclusion] using h

end WeierstrassCurve.Velu
