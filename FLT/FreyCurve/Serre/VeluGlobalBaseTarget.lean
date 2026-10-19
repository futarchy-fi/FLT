/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffinePointNaturality
public import FLT.FreyCurve.Serre.VeluGlobalTargetTransport

/-!
# The original global Vélu morphism viewed over the original target field

The exact target equation is transported before coefficient projection.
Its values are the original classical Vélu points on the original base target.
For a stable kernel, these actual scheme-point values commute with Galois.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [CharZero L] [IsAlgClosed L] [DecidableEq L]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup (E.map (algebraMap K L)).toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  (V : WeierstrassCurve K)
  (hV : V.map (algebraMap K L) = curve (E.map (algebraMap K L)) G)

local notation "EL" => E.map (algebraMap K L)

/-- Cache the original finite group in the classical base-change presentation. -/
local instance baseTargetFintype :
    Fintype (show AddSubgroup (E.toAffine.baseChange L).Point from G) :=
  inferInstanceAs (Fintype G)

/-- The actual geometric map followed by projection to the exact original base target. -/
def veluGlobalToBaseTarget : integralCurve EL ⟶ integralCurve V :=
  veluGlobalToEquation EL G hodd (V.map (algebraMap K L)) hV ≫
    integralCoefficientMorphism V

/-- The map to the original target retains the actual coefficient map on the base. -/
@[reassoc] theorem veluGlobalToBaseTarget_base :
    veluGlobalToBaseTarget E G hodd V hV ≫ integralCurveStructure V =
      integralCurveStructure EL ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [veluGlobalToBaseTarget, Category.assoc, integralCoefficientMorphism_structure,
    veluGlobalToEquation_base_assoc]

/-- The identity still maps to the original base target's identity. -/
@[reassoc] theorem veluGlobalToBaseTarget_zero :
    integralCurveZero EL ≫ veluGlobalToBaseTarget E G hodd V hV =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ integralCurveZero V := by
  rw [veluGlobalToBaseTarget, veluGlobalToEquation_zero_assoc,
    integralCoefficientMorphism_zero]

/-- Every original affine point retains its exact Vélu coordinates on the base target. -/
@[reassoc] theorem veluGlobalToBaseTarget_pointMap
    (h : ∀ P, P ∉ G → (V.map (algebraMap K L)).toAffine.Nonsingular
      (xMap EL G P) (yMap EL G P)) (P : (EL).toAffine.Point) :
    (affineSmoothPoint EL P ≫ (integralSmoothOpen EL).ι) ≫
        veluGlobalToBaseTarget E G hodd V hV =
      affineSmoothPoint V (pointMap EL G (V.map (algebraMap K L)) h P) ≫
        (integralSmoothOpen V).ι := by
  rw [veluGlobalToBaseTarget, ← Category.assoc,
    veluGlobalToEquation_pointMap EL G hodd _ hV h P,
    affineSmoothPoint_coefficient]

/-- The actual scheme-point values satisfy Galois compatibility for a stable kernel. -/
theorem veluGlobalToBaseTarget_galois_points
    (h : ∀ P, P ∉ G → (V.map (algebraMap K L)).toAffine.Nonsingular
      (xMap EL G P) (yMap EL G P))
    (hG : ∀ (g : L ≃ₐ[K] L) P, P ∈ G →
      Affine.Point.map (W' := E.toAffine) g.toAlgHom P ∈ G)
    (g : L ≃ₐ[K] L) (P : (EL).toAffine.Point) :
    (affineSmoothPoint EL (Affine.Point.map (W' := E.toAffine) g.toAlgHom P) ≫
        (integralSmoothOpen EL).ι) ≫ veluGlobalToBaseTarget E G hodd V hV =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        (affineSmoothPoint EL P ≫ (integralSmoothOpen EL).ι) ≫
          veluGlobalToBaseTarget E G hodd V hV := by
  rw [veluGlobalToBaseTarget_pointMap E G hodd V hV h,
    veluGlobalToBaseTarget_pointMap E G hodd V hV h]
  have hm : pointMap EL G (V.map (algebraMap K L)) h
      (Affine.Point.map (W' := E.toAffine) g.toAlgHom P) =
        Affine.Point.map (W' := V.toAffine) g.toAlgHom
          (pointMap EL G (V.map (algebraMap K L)) h P) := pointMap_map E G V h hG g P
  rw [hm]
  exact (affineSmoothPoint_natural V g.toAlgHom _).symm

end WeierstrassCurve.Velu
