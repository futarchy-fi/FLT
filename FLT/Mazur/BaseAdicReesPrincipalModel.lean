/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModuleLocalization
public import FLT.Mazur.AffineTildeBaseChangeUnit

/-!
# Principal-overlap isomorphisms of the actual relative coherent models

The original relative restriction induces an isomorphism from the actual
pullback of the larger affine model to the smaller model. The proof uses
the established whole-module scalar-extension comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (M : X.Modules)

/-- The actual extended-power module over its own relative tensor ring. -/
def nativeModule (V : X.affineOpens) :
    let _ := chartAlgebra f V
    ModuleCat (Γ(X, V.1) ⊗[R] reesAlgebra J) := by
  let _ := chartAlgebra f V
  let _ := Rees.relativeModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J
  exact ModuleCat.of _ (Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J)

/-- Passing to the fixed-chart action on the chart itself keeps each original coefficient. -/
def nativeSelfEquiv (V : X.affineOpens) :
    let _ := chartAlgebra f V
    let _ := chartTensorModule f J M V V le_rfl
    nativeModule f J M V ≃ₗ[Γ(X, V.1) ⊗[R] reesAlgebra J]
      chartModule f J M V V le_rfl := by
  let _ := chartAlgebra f V
  let _ := chartTensorModule f J M V V le_rfl
  refine { AddEquiv.refl _ with map_smul' := ?_ }
  intro r s
  exact (chartTensorModule_self_smul f J M V r s).symm

/-- The original coefficient map as a morphism between the actual relative modules. -/
def nativeRestriction {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    nativeModule f J M V ⟶
      (ModuleCat.restrictScalars (relativeRingRestriction f J h).toRingHom).obj
        (nativeModule f J M U) := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  let _ := Rees.relativeModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J
  let _ := Rees.relativeModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J
  let _ : Module (Γ(X, V.1) ⊗[R] reesAlgebra J) (nativeModule f J M U) :=
    Module.compHom (nativeModule f J M U) (relativeRingRestriction f J h).toRingHom
  exact ModuleCat.ofHom (show nativeModule f J M V →ₗ[Γ(X, V.1) ⊗[R] reesAlgebra J]
    (ModuleCat.restrictScalars (relativeRingRestriction f J h).toRingHom).obj
      (nativeModule f J M U) from
    { toFun := fun s ↦ relativeRestriction f J M h s
      map_add' := (relativeRestriction f J M h).map_add
      map_smul' := (relativeRestriction f J M h).map_smulₛₗ })

variable [IsLocallyNoetherian X] [M.IsFinitePresentation]

/-- The original module restriction is scalar extension over its actual tensor-ring map. -/
theorem nativeRestriction_isBaseChange (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    let _ := (relativeRingRestriction f J (U := U) (V := V)
      (X.basicOpen_le r)).toRingHom.toAlgebra
    let _ := AffineTildeBaseChangeIso.restrictScalarTower
      (CommRingCat.ofHom (relativeRingRestriction f J (U := U) (V := V)
        (X.basicOpen_le r)).toRingHom) (nativeModule f J M U)
    IsBaseChange (Γ(X, U.1) ⊗[R] reesAlgebra J)
      (nativeRestriction f J M (U := U) (V := V) (X.basicOpen_le r)).hom := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  let _ := (relativeRingRestriction f J (U := U) (V := V)
    (X.basicOpen_le r)).toRingHom.toAlgebra
  let _ : Module (Γ(X, U.1) ⊗[R] reesAlgebra J)
      (chartModule f J M V U (X.basicOpen_le r)) :=
    Rees.relativeModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J
  let _ := chartTensorModule f J M V V le_rfl
  let _ := chartTensorModule f J M V U (X.basicOpen_le r)
  let _ : IsScalarTower (Γ(X, V.1) ⊗[R] reesAlgebra J)
      (Γ(X, U.1) ⊗[R] reesAlgebra J) (chartModule f J M V U (X.basicOpen_le r)) :=
    ⟨fun a b m ↦ mul_smul (relativeRingRestriction f J (U := U) (V := V)
      (X.basicOpen_le r) a) b m⟩
  exact IsBaseChange.comp_equiv (nativeSelfEquiv f J M V)
    (chartTensorRestriction f J M V (U := U) (X.basicOpen_le r) le_rfl
      (X.basicOpen_le r)) (chartTensorRestriction_isBaseChange f J M V r)

variable [IsNoetherianRing R]

/-- The actual coherent model on a principal chart is the pullback of the larger model. -/
def principalModelIso (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    (pullback (Spec.map (CommRingCat.ofHom
      (relativeRingRestriction f J (U := U) (V := V) (X.basicOpen_le r)).toRingHom))).obj
        (modelSheaf f J V M) ≅ modelSheaf f J U M := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  exact AffineTildeBaseChangeIso.iso
    (CommRingCat.ofHom (relativeRingRestriction f J (U := U) (V := V)
      (X.basicOpen_le r)).toRingHom) (nativeModule f J M V) (nativeModule f J M U)
    (nativeRestriction f J M (X.basicOpen_le r)) (nativeRestriction_isBaseChange f J M V r)

omit [IsNoetherianRing R] in
/-- The principal model isomorphism is induced by the original relative coefficient map. -/
lemma principalModelIso_hom (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    (principalModelIso f J M V r).hom = AffineTildeSemilinearMap.map
      (CommRingCat.ofHom (relativeRingRestriction f J (U := U) (V := V)
        (X.basicOpen_le r)).toRingHom) (nativeModule f J M V) (nativeModule f J M U)
      (nativeRestriction f J M (X.basicOpen_le r)) := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  exact AffineTildeBaseChangeIso.iso_hom _ _ _ _ _

omit [IsNoetherianRing R] in
/-- The principal model isomorphism retains each original section under the pullback unit. -/
lemma principalModelIso_unit (V : X.affineOpens) (r : Γ(X, V.1))
    (s : nativeModule f J M V) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    let φ := CommRingCat.ofHom (relativeRingRestriction f J (U := U) (V := V)
      (X.basicOpen_le r)).toRingHom
    (principalModelIso f J M V r).hom.app ⊤
      (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (modelSheaf f J V M)).app ⊤
        (tilde.toOpen (R := .of (Γ(X, V.1) ⊗[R] reesAlgebra J))
          (nativeModule f J M V) ⊤ s)) =
      tilde.toOpen (R := .of (Γ(X, U.1) ⊗[R] reesAlgebra J))
        (nativeModule f J M U) ⊤
        (nativeRestriction f J M (U := U) (V := V) (X.basicOpen_le r) s) := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  exact AffineTildeBaseChangeIso.iso_unit
    (CommRingCat.ofHom (relativeRingRestriction f J (U := U) (V := V)
      (X.basicOpen_le r)).toRingHom) (nativeModule f J M V) (nativeModule f J M U)
    (nativeRestriction f J M (X.basicOpen_le r)) (nativeRestriction_isBaseChange f J M V r) s

end FLT.Mazur.BaseAdicRees
