/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluTranslatedInfinityGeneric

/-!
# The original Vélu rational map on translated infinity neighborhoods

Kernel invariance identifies the regular morphism on each transported
neighborhood with the original rational map of the actual cubics.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic] (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  {u v : K} (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∈ G)

/-- The explicit regular extension as a partial map of the actual cubics. -/
def veluTranslatedInfinityPartialMap :
    (integralCurve E).PartialMap (integralCurve (curve E G)) where
  domain := (veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).opensRange
  dense_domain := veluTranslatedInfinityOpenImmersion_dense E G hQ
  hom := (veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).isoOpensRange.inv ≫
    veluInfinityRegularMorphism E G hodd

/-- The generic-stalk restriction through the open is the constructed generic factorization. -/
theorem veluTranslatedInfinityOpen_generic
    (hx : genericPoint (integralCurve E) ∈
      (veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).opensRange) :
    (veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).opensRange.fromSpecStalkOfMem _ hx ≫
        (veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).isoOpensRange.inv =
      veluTranslatedInfinityGenericPoint E G hQ := by
  apply (cancel_mono (veluTranslatedInfinityOpenImmersion E G (.some u v hQ))).mp
  rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp,
    Scheme.Opens.fromSpecStalkOfMem_ι, veluTranslatedInfinityGenericPoint_source]

variable [IsAlgClosed K]

include hQG

/-- The explicit partial map retains the original actual generic Vélu map. -/
theorem veluTranslatedInfinityPartialMap_fromFunctionField :
    (veluTranslatedInfinityPartialMap E G hodd hQ).fromFunctionField =
      veluSchemeGenericMorphism E G hodd := by
  change Scheme.Opens.fromSpecStalkOfMem
    (veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).opensRange _ _ ≫
    ((veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).isoOpensRange.inv ≫
    veluInfinityRegularMorphism E G hodd) = _
  rw [← Category.assoc, veluTranslatedInfinityOpen_generic,
    veluTranslatedInfinityGenericPoint_target E G hQ hodd hQG]

/-- This explicit regular extension represents precisely the original Vélu rational map. -/
theorem veluTranslatedInfinityPartialMap_toRationalMap :
    (veluTranslatedInfinityPartialMap E G hodd hQ).toRationalMap =
      veluSchemeRationalMap E G hodd := by
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    veluTranslatedInfinityPartialMap_fromFunctionField E G hodd hQ hQG,
    veluSchemeRationalMap_fromFunctionField]

/-- The original rational map is defined throughout the explicit infinity neighborhood. -/
theorem veluTranslatedInfinityOpen_le_rationalDomain :
    (veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).opensRange ≤
      (veluSchemeRationalMap E G hodd).domain := by
  rw [← veluTranslatedInfinityPartialMap_toRationalMap E G hodd hQ hQG]
  exact (veluTranslatedInfinityPartialMap E G hodd hQ).le_domain_toRationalMap

/-- The original negative kernel point belongs to the original rational map's domain. -/
theorem veluNegativeKernelPoint_mem_rationalDomain (x : Spec (.of K)) :
    (affineSmoothPoint E (-Affine.Point.some u v hQ) ≫ (integralSmoothOpen E).ι) x ∈
      (veluSchemeRationalMap E G hodd).domain :=
  veluTranslatedInfinityOpen_le_rationalDomain E G hodd hQ hQG
    (veluTranslatedInfinityPoint_mem_open E G (.some u v hQ) x)

end WeierstrassCurve.Velu
