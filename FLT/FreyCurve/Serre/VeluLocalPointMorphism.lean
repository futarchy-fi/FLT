/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalPointTransport
public import FLT.Mazur.WeierstrassLocalGenericProjection

/-!
# Transporting a known scheme-point value through actual local models

The Cartesian local projection detects the value on each specified transported
point. Only the original morphism square and original point value are inputs.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L R : Type} [Field K] [Field L] [CommRing R]
  [Algebra K L] [Algebra R L] [DecidableEq K] [DecidableEq L]
  (E V : WeierstrassCurve K) [E.IsElliptic] [V.IsElliptic]
  (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap K L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap K L) = U.map (algebraMap R L))
  (f : integralCurve E ⟶ integralCurve V)
  (g : integralCurve (W.map (algebraMap R L)) ⟶ integralCurve (U.map (algebraMap R L)))
  (hg : g ≫ integralCurveStructure (U.map (algebraMap R L)) =
    integralCurveStructure (W.map (algebraMap R L)))
  (hsq : g ≫ localGenericProjection V U D hD = localGenericProjection E W C hC ≫ f)

include hg hsq in
/-- A known original scheme-point value gives the exact specified local point value. -/
@[reassoc] theorem ellipticExtensionPointHom_morphism
    (P : (E.map (algebraMap K K)).toAffine.Point)
    (Q : (V.map (algebraMap K K)).toAffine.Point)
    (hPQ : (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫ f =
      affineSmoothPoint V Q ≫ (integralSmoothOpen V).ι) :
    (affineSmoothPoint (W.map (algebraMap R L))
        (ellipticExtensionPointHom (K := K) E W C hC P) ≫
          (integralSmoothOpen (W.map (algebraMap R L))).ι) ≫ g =
      affineSmoothPoint (U.map (algebraMap R L))
        (ellipticExtensionPointHom (K := K) V U D hD Q) ≫
          (integralSmoothOpen (U.map (algebraMap R L))).ι := by
  have he := ellipticExtensionPointHom_rational E W C hC P
  have hv := ellipticExtensionPointHom_rational V U D hD Q
  change _ ≫ localGenericProjection E W C hC = _ at he
  change _ ≫ localGenericProjection V U D hD = _ at hv
  apply localGenericProjection_hom_ext V U D hD
  · rw [Category.assoc, hsq, ← Category.assoc, he, Category.assoc, hPQ, hv]
  · rw [Category.assoc, hg]
    change affineSmoothPoint _ _ ≫ integralSmoothStructure _ =
      affineSmoothPoint _ _ ≫ integralSmoothStructure _
    rw [affineSmoothPoint_structure, affineSmoothPoint_structure]

end WeierstrassCurve.Velu
