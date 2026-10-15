/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# A finite scheme carrying the unchanged first-order node correspondence

The finite error algebra carries the two actual node maps. Its spectrum
therefore gives a finite correspondence over the original source node, with
the target map retaining the original action on every branch function.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "B" => ChartRing (parameter (R) 1)
local notation "C" => firstNodeBranchSubalgebra (R)
local notation "β" => firstNodeBranchPair (R)
local notation "F" => completeIdentityFirstActionBranchEquiv K n h i
local notation "E" => completeIdentityFirstErrorAlgebra K n h i

/-- The actual source node map into the constructed finite error algebra. -/
def completeIdentityFirstGraphSource : (B) →ₐ[S] (E) :=
  (IsScalarTower.toAlgHom (S) (C) (E)).comp (firstNodeBranchEquiv (R)).toAlgHom

/-- The source map retains the entire original branch pair. -/
theorem completeIdentityFirstGraphSource_apply (z : B) :
    (completeIdentityFirstGraphSource K n h i z).val = (β) z := rfl

/-- The original action also factors through this same concrete finite algebra. -/
def completeIdentityFirstGraphTarget : (B) →ₐ[S] (E) :=
  ((F).toAlgHom.comp (β)).codRestrict ((E).restrictScalars (S))
    (fun z ↦ completeIdentityFirstErrorAlgebra_target K n h i ⟨z, rfl⟩)

/-- The target map is the unchanged original action on every original node function. -/
theorem completeIdentityFirstGraphTarget_apply (z : B) :
    (completeIdentityFirstGraphTarget K n h i z).val = (F) ((β) z) := rfl

/-- The original source map is finite, using the two proved square-zero error generators. -/
theorem completeIdentityFirstGraphSource_finite :
    @RingHom.Finite (B) (E) inferInstance inferInstance
      (completeIdentityFirstGraphSource K n h i).toRingHom := by
  let _ : CommRing (E) := inferInstance
  change RingHom.Finite ((algebraMap (C) (E)).comp
    (firstNodeBranchEquiv (R)).toRingEquiv.toRingHom)
  have he : (algebraMap (C) (E)).Finite :=
    RingHom.finite_algebraMap.mpr (completeIdentityFirstErrorAlgebra_finite K n h i)
  exact he.comp (firstNodeBranchEquiv (R)).toRingEquiv.finite

/-- The spectrum of the actual finite source-target graph algebra. -/
def completeIdentityFirstGraphScheme : Scheme := Spec (CommRingCat.of (E))

/-- The finite correspondence projects to the unchanged original node scheme. -/
def completeIdentityFirstGraphSchemeSource :
    completeIdentityFirstGraphScheme K n h i ⟶ Spec (CommRingCat.of (B)) :=
  Spec.map (CommRingCat.ofHom (completeIdentityFirstGraphSource K n h i).toRingHom)

/-- This projection is finite without any assumed preservation of the original node algebra. -/
instance completeIdentityFirstGraphSchemeSource_finite :
    IsFinite (completeIdentityFirstGraphSchemeSource K n h i) := by
  rw [completeIdentityFirstGraphSchemeSource, IsFinite.SpecMap_iff]
  exact completeIdentityFirstGraphSource_finite K n h i

/-- The same correspondence has its actual original-action target map. -/
def completeIdentityFirstGraphSchemeTarget :
    completeIdentityFirstGraphScheme K n h i ⟶ Spec (CommRingCat.of (B)) :=
  Spec.map (CommRingCat.ofHom (completeIdentityFirstGraphTarget K n h i).toRingHom)

end FLT.Mazur.PolygonInfinitesimalStages
