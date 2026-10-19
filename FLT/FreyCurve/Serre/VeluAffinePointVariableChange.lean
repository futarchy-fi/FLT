/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffinePointNaturality
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction
public import FLT.Mazur.WeierstrassVariableChangeZero
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Actual variable changes retain classical affine scheme points

The global cubic isomorphism acts by the original affine coordinate formulas,
including the infinity section. Its inverse therefore realizes the prescribed
point-group transport on the actual cubic, not merely on coordinate tuples.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [DecidableEq K]
  (E V : WeierstrassCurve K) (C : VariableChange K) (hC : C • E = V)

/-- The actual cubic isomorphism agrees with the original forward affine point change. -/
@[reassoc] theorem affineSmoothPoint_variableChange [E.IsElliptic]
    (P : V.toAffine.Point) :
    (affineSmoothPoint V P ≫ (integralSmoothOpen V).ι) ≫
        (integralVariableChangeIso E V C hC).hom =
      affineSmoothPoint E
        (Affine.Point.equivVariableChange E C ((Affine.Point.equivOfEq hC).symm P)) ≫
          (integralSmoothOpen E).ι := by
  subst V
  cases P with
  | zero =>
    change (affineSmoothPoint (C • E) (0 : (C • E).toAffine.Point) ≫ _) ≫ _ =
      affineSmoothPoint E (0 : E.toAffine.Point) ≫ _
    rw [affineSmoothPoint_zero, affineSmoothPoint_zero, Category.assoc,
      integralVariableChangeIso_zero]
  | some x y h =>
    change (affineSmoothPoint (C • E) (.some x y h) ≫ _) ≫ _ =
      affineSmoothPoint E (Affine.Point.equivVariableChange E C (.some x y h)) ≫ _
    rw [Affine.Point.equivVariableChange_some, affineSmoothPoint_some,
      affineSmoothPoint_some, integralChartPoint, integralChartPoint, Category.assoc,
      integralVariableChangeIso_affine, ← Category.assoc]
    congr 1
    apply affineVariableChangeIso_section
    · simp only [evaluation_coord]
      rfl
    · simp only [evaluation_coord]
      rfl

/-- The inverse cubic isomorphism realizes the specified inverse point-group change. -/
@[reassoc] theorem affineSmoothPoint_variableChange_inv [E.IsElliptic]
    (P : E.toAffine.Point) :
    (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫
        (integralVariableChangeIso E V C hC).inv =
      affineSmoothPoint V
        (Affine.Point.equivOfEq hC ((Affine.Point.equivVariableChange E C).symm P)) ≫
          (integralSmoothOpen V).ι := by
  apply (cancel_mono (integralVariableChangeIso E V C hC).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, affineSmoothPoint_variableChange]
  simp only [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

end WeierstrassCurve.Velu
