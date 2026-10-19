/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineGenericRestriction

/-!
# An explicit regular representative of the original Vélu rational map

The regular morphism on the denominator open represents the previously
constructed rational map of the actual source and target cubics.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The explicit regular extension as a partial map of the actual cubics. -/
def veluAffinePartialMap : (integralCurve E).PartialMap (integralCurve (curve E G)) where
  domain := (veluAffineOpenImmersion E G).opensRange
  dense_domain := veluAffineOpenImmersion_dense E G
  hom := (veluAffineOpenImmersion E G).isoOpensRange.inv ≫ veluAffineRegularMorphism E G hodd

/-- The generic-stalk restriction through the open is the constructed generic factorization. -/
theorem veluAffineOpen_generic
    (hx : genericPoint (integralCurve E) ∈ (veluAffineOpenImmersion E G).opensRange) :
    (veluAffineOpenImmersion E G).opensRange.fromSpecStalkOfMem _ hx ≫
        (veluAffineOpenImmersion E G).isoOpensRange.inv = veluAffineGenericPoint E G := by
  apply (cancel_mono (veluAffineOpenImmersion E G)).mp
  rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp,
    Scheme.Opens.fromSpecStalkOfMem_ι, veluAffineGenericPoint_source]

/-- The explicit partial map retains the original actual generic Vélu map. -/
theorem veluAffinePartialMap_fromFunctionField :
    (veluAffinePartialMap E G hodd).fromFunctionField = veluSchemeGenericMorphism E G hodd := by
  change (veluAffineOpenImmersion E G).opensRange.fromSpecStalkOfMem _ _ ≫
    ((veluAffineOpenImmersion E G).isoOpensRange.inv ≫
    veluAffineRegularMorphism E G hodd) = _
  rw [← Category.assoc, veluAffineOpen_generic, veluAffineGenericPoint_target]

/-- This explicit regular extension represents precisely the original Vélu rational map. -/
theorem veluAffinePartialMap_toRationalMap :
    (veluAffinePartialMap E G hodd).toRationalMap = veluSchemeRationalMap E G hodd := by
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    veluAffinePartialMap_fromFunctionField, veluSchemeRationalMap_fromFunctionField]

/-- The original rational map is defined throughout the explicit denominator open. -/
theorem veluAffineOpen_le_rationalDomain :
    (veluAffineOpenImmersion E G).opensRange ≤ (veluSchemeRationalMap E G hodd).domain := by
  rw [← veluAffinePartialMap_toRationalMap]
  exact (veluAffinePartialMap E G hodd).le_domain_toRationalMap

end WeierstrassCurve.Velu
