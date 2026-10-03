/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonHZeroIncidence
public import FLT.Mazur.PolygonNormalizationExact
public import FLT.Mazur.ModuleCohomologyExact
/-!
# Constant global sections of a polygon

The normalization inclusion embeds H0 in the component constants. Its image
lies in the incidence kernel, and canonical base constants give every vector
in that kernel.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonConstantSections
open FCurve PolygonPinching PolygonStructureInclusion PolygonBranchDifferenceSheaf
open PolygonNormalizationHZero
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
local notation "S" => PolygonNormalizationComplex.complex K n hn p q h
/-- The structure inclusion on H0, in component coordinates. -/
def componentsH0 : H0 C.hom →ₗ[K] (Fin n → K) :=
  (normalizationEquiv K n p).toLinearMap.comp
    ((moduleScalarHMap C.hom (inclusion K n p) 0).comp
      (moduleScalarHUnitEquiv C.hom 0).symm.toLinearMap)
omit [NeZero n] in
/-- The coordinate definition of the H0 inclusion. -/
theorem componentsH0_apply (x : H0 C.hom) : componentsH0 K n p x =
    normalizationEquiv K n p (moduleScalarHMap C.hom (inclusion K n p) 0
      ((moduleScalarHUnitEquiv C.hom 0).symm x)) := rfl
include h in
/-- The actual normalization inclusion is injective on H0. -/
theorem componentsH0_injective : Function.Injective (componentsH0 K n p) := by
  have hs : (moduleAbelianComplex S).ShortExact :=
    PolygonNormalizationExact.abelianSheaf_shortExact K n hn p q h
  exact (normalizationEquiv K n p).injective.comp
    ((moduleScalarHMap_zero_injective S hs C.hom).comp
      (moduleScalarHUnitEquiv C.hom 0).symm.injective)
omit [NeZero n] in
/-- Component coordinates use the specified global-section restrictions. -/
theorem coordinate (x : H0 C.hom) (i : Fin n) :
    structureScalarMap (ProjectiveLine.toBase K) (componentsH0 K n p x i) =
      (componentι K n i).left.appTop (p.left.appTop (scalarH0Equiv C.hom x)) := by
  rw [componentsH0_apply, normalization_coordinate]
  change (componentι K n i).left.appTop
    (moduleH0Equiv _ (moduleHMap (inclusion K n p) 0 _)) = _
  rw [moduleH0Equiv_naturality]
  rfl
omit [NeZero n] in
/-- Canonical base constants give the constant component vector. -/
theorem constants_coordinate (a : K) :
    componentsH0 K n p (scalarH0Constants C.hom a) = PolygonIncidence.constant K n a := by
  ext i
  apply (ProjectiveLineConstantSections.constant_sections K).1
  rw [coordinate, scalarH0Equiv_constants]
  have hw : ((componentι K n i) ≫ p).left ≫ C.hom = ProjectiveLine.toBase K :=
    ((componentι K n i) ≫ p).w
  change (((componentι K n i) ≫ p).left ≫ C.hom).appTop ((Scheme.ΓSpecIso (.of K)).inv a) =
    (ProjectiveLine.toBase K).appTop ((Scheme.ΓSpecIso (.of K)).inv a)
  rw [hw]
  rfl
include h in
/-- Polygon global functions have zero branch difference. -/
theorem difference_zero (x : H0 C.hom) :
    PolygonIncidence.difference K hn (componentsH0 K n p x) = 0 := by
  have hs : (moduleAbelianComplex S).ShortExact :=
    PolygonNormalizationExact.abelianSheaf_shortExact K n hn p q h
  have he := moduleScalarH_exact₂ S hs C.hom 0
  have hz := (he (moduleScalarHMap C.hom (inclusion K n p) 0
    ((moduleScalarHUnitEquiv C.hom 0).symm x))).mpr ⟨_, rfl⟩
  rw [componentsH0_apply, ← PolygonCohomologyIncidence.difference_coordinates K n hn p q h]
  exact (congrArg (nodeEquiv K n q) hz).trans (map_zero _)
include h in
/-- The specified structure morphism has exactly the base-field global sections. -/
theorem constants : HasConstantGlobalSections C.hom := by
  rw [hasConstantGlobalSections_iff]
  constructor
  · intro a b hab
    have he := congrArg (fun x ↦ componentsH0 K n p x ⟨0, hn⟩) hab
    simpa only [constants_coordinate, PolygonIncidence.constant_apply] using he
  · intro x
    let a := componentsH0 K n p x ⟨0, hn⟩
    refine ⟨a, componentsH0_injective K n hn p q h ?_⟩
    rw [constants_coordinate]
    funext i
    exact (PolygonIncidence.eq_initial_of_difference_eq_zero hn _
      (difference_zero K n hn p q h x) i).symm
end FLT.Mazur.PolygonConstantSections
