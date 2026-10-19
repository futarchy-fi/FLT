/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityGenericRestriction

/-!
# An explicit regular representative of the original Vélu rational map

The regular morphism on the infinity neighborhood represents the previously
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
def veluInfinityPartialMap : (integralCurve E).PartialMap (integralCurve (curve E G)) where
  domain := (veluInfinityOpenImmersion E G).opensRange
  dense_domain := veluInfinityOpenImmersion_dense E G
  hom := (veluInfinityOpenImmersion E G).isoOpensRange.inv ≫ veluInfinityRegularMorphism E G hodd

/-- The generic-stalk restriction through the open is the constructed generic factorization. -/
theorem veluInfinityOpen_generic
    (hx : genericPoint (integralCurve E) ∈ (veluInfinityOpenImmersion E G).opensRange) :
    (veluInfinityOpenImmersion E G).opensRange.fromSpecStalkOfMem _ hx ≫
        (veluInfinityOpenImmersion E G).isoOpensRange.inv = veluInfinityGenericPoint E G := by
  apply (cancel_mono (veluInfinityOpenImmersion E G)).mp
  rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp,
    Scheme.Opens.fromSpecStalkOfMem_ι, veluInfinityGenericPoint_source]

/-- The explicit partial map retains the original actual generic Vélu map. -/
theorem veluInfinityPartialMap_fromFunctionField :
    (veluInfinityPartialMap E G hodd).fromFunctionField = veluSchemeGenericMorphism E G hodd := by
  change (veluInfinityOpenImmersion E G).opensRange.fromSpecStalkOfMem _ _ ≫
    ((veluInfinityOpenImmersion E G).isoOpensRange.inv ≫
    veluInfinityRegularMorphism E G hodd) = _
  rw [← Category.assoc, veluInfinityOpen_generic, veluInfinityGenericPoint_target]

/-- This explicit regular extension represents precisely the original Vélu rational map. -/
theorem veluInfinityPartialMap_toRationalMap :
    (veluInfinityPartialMap E G hodd).toRationalMap = veluSchemeRationalMap E G hodd := by
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    veluInfinityPartialMap_fromFunctionField, veluSchemeRationalMap_fromFunctionField]

/-- The original rational map is defined throughout the explicit infinity neighborhood. -/
theorem veluInfinityOpen_le_rationalDomain :
    (veluInfinityOpenImmersion E G).opensRange ≤ (veluSchemeRationalMap E G hodd).domain := by
  rw [← veluInfinityPartialMap_toRationalMap]
  exact (veluInfinityPartialMap E G hodd).le_domain_toRationalMap

/-- The original source infinity point is in the domain of the original rational map. -/
theorem veluInfinityPoint_mem_rationalDomain (x : Spec (.of K)) :
    (Spec.map (CommRingCat.ofHom (infinityEvaluation E).toRingHom) ≫
      integralCurveChart E 1) x ∈ (veluSchemeRationalMap E G hodd).domain := by
  rw [← veluInfinityPointLift_source E G]
  exact veluInfinityOpen_le_rationalDomain E G hodd ⟨veluInfinityPointLift E G x, rfl⟩

end WeierstrassCurve.Velu
