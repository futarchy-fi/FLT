/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffinePointVariableChange
public import FLT.Mazur.EllipticExtensionPrimeSubgroup

/-!
# The specified local point transport on the actual generic cubic

The original field embedding and inverse variable change agree with their
scheme morphisms. This keeps both the exact local equation and the original
rational point when passing to a local generic model.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L R : Type} [Field K] [Field L] [CommRing R]
  [Algebra K L] [Algebra R L] [DecidableEq K] [DecidableEq L]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (W : WeierstrassCurve R) (C : VariableChange L)
  (hC : C • E.map (algebraMap K L) = W.map (algebraMap R L))

/-- The prescribed local point is the actual inverse cubic change of its scalar extension. -/
theorem ellipticExtensionPointHom_scheme (P : (E.map (algebraMap K K)).toAffine.Point) :
    affineSmoothPoint (W.map (algebraMap R L))
        (ellipticExtensionPointHom (K := K) E W C hC P) ≫
          (integralSmoothOpen (W.map (algebraMap R L))).ι =
      (affineSmoothPoint (E.map (algebraMap K L))
        (Affine.Point.map (W' := E.toAffine) (Algebra.ofId K L) P) ≫
          (integralSmoothOpen (E.map (algebraMap K L))).ι) ≫
            (integralVariableChangeIso _ _ C hC).inv :=
  (affineSmoothPoint_variableChange_inv _ _ C hC _).symm

/-- Applying the actual local change returns the original coefficient-extended point. -/
@[reassoc] theorem ellipticExtensionPointHom_variableChange
    (P : (E.map (algebraMap K K)).toAffine.Point) :
    (affineSmoothPoint (W.map (algebraMap R L))
        (ellipticExtensionPointHom (K := K) E W C hC P) ≫
          (integralSmoothOpen (W.map (algebraMap R L))).ι) ≫
            (integralVariableChangeIso _ _ C hC).hom =
      affineSmoothPoint (E.map (algebraMap K L))
        (Affine.Point.map (W' := E.toAffine) (Algebra.ofId K L) P) ≫
          (integralSmoothOpen (E.map (algebraMap K L))).ι := by
  rw [ellipticExtensionPointHom_scheme, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The specified local point recovers the original point over the original spectrum map. -/
@[reassoc] theorem ellipticExtensionPointHom_rational
    (P : (E.map (algebraMap K K)).toAffine.Point) :
    (affineSmoothPoint (W.map (algebraMap R L))
        (ellipticExtensionPointHom (K := K) E W C hC P) ≫
          (integralSmoothOpen (W.map (algebraMap R L))).ι) ≫
            (integralVariableChangeIso _ _ C hC).hom ≫ integralCoefficientMorphism E =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) := by
  rw [← Category.assoc, ellipticExtensionPointHom_variableChange,
    affineSmoothPoint_coefficient]
  exact (affineSmoothPoint_natural E (Algebra.ofId K L) P).symm

end WeierstrassCurve.Velu
