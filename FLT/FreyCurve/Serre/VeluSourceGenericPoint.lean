/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSourceSchemeFunctionField

/-!
# The original source formulas recover the actual generic point

The field comparison commutes with the original source chart evaluation and
therefore with the canonical map from the cubic's generic stalk.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- The affine field comparison preserves every original coordinate-ring function. -/
theorem sourceAffineFunctionFieldEquiv_chart (a : Coordinate E 2) :
    sourceAffineFunctionFieldEquiv E (sourceGenericChart E a) =
      algebraMap (Coordinate E 2) (chartScheme E 2).functionField a :=
  (sourceAffineFunctionFieldEquiv E).commutes a

/-- The affine generic-point map is exactly the original coordinate evaluation. -/
@[reassoc] theorem sourceAffineFunctionFieldEquiv_spec :
    Spec.map (CommRingCat.ofHom (sourceAffineFunctionFieldEquiv E).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (sourceGenericChart E).toRingHom) =
      (chartScheme E 2).fromSpecStalk (genericPoint (chartScheme E 2)) := by
  rw [← Spec.map_comp, Spec.fromSpecStalk_eq']
  congr 1
  apply CommRingCat.hom_ext
  exact (sourceAffineFunctionFieldEquiv E).toAlgHom.comp_algebraMap

/-- The field identification retains the canonical generic point of the whole cubic. -/
@[reassoc] theorem sourceSchemeFunctionFieldEquiv_spec :
    Spec.map (CommRingCat.ofHom (sourceSchemeFunctionFieldEquiv E).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (sourceGenericChart E).toRingHom) ≫
          integralCurveChart E 2 =
      (integralCurve E).fromSpecStalk (genericPoint (integralCurve E)) := by
  change Spec.map
    (CommRingCat.ofHom (sourceAffineFunctionFieldEquiv E).toRingHom ≫
      (sourceCurveFunctionFieldIso E).inv) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, sourceAffineFunctionFieldEquiv_spec_assoc,
    ← sourceCurveFunctionFieldIso_fromSpecStalk, ← Category.assoc, ← Spec.map_comp,
    Iso.hom_inv_id, Spec.map_id, Category.id_comp]

end WeierstrassCurve.Velu
