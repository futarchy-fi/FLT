/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesCocycle
public import FLT.Mazur.BaseAdicReesModuleChart
public import FLT.Mazur.BaseAdicReesOverlap
public import FLT.Mazur.ReesRelativeScalarTower

/-!
# Relative tensor action over a fixed source chart

The original relative module restrictions are linear over the larger tensor
ring. Its constant scalars retain the original chart module structure.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (M : X.Modules) (V : X.affineOpens)

/-- Relative power modules with the tensor action from a fixed larger chart. -/
@[instance_reducible]
def chartTensorModule (U : X.affineOpens) (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    Module (Γ(X, V.1) ⊗[R] reesAlgebra J) (chartModule f J M V U h) := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  let _ := Rees.relativeModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J
  exact Module.compHom (Rees.extendedModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J)
    (relativeRingRestriction f J h).toRingHom

/-- On the ambient chart, the tensor action is the original relative quotient action. -/
lemma chartTensorModule_self_smul
    (r : let _ := chartAlgebra f V; Γ(X, V.1) ⊗[R] reesAlgebra J)
    (s : chartModule f J M V V le_rfl) :
    let _ := chartAlgebra f V
    let _ := chartTensorModule f J M V V le_rfl
    r • s = Rees.relativeMap J r •
      (show Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J from s) := by
  let _ := chartAlgebra f V
  let _ := chartTensorModule f J M V V le_rfl
  change Rees.relativeMap J (relativeRingRestriction f J (U := V) le_rfl r) •
    (show Rees.extendedModule (S := Γ(X, V.1)) (M := Γ(M, V.1)) J from s) = _
  have he := AlgHom.congr_fun (relativeRingRestriction_id f J (U := V)) r
  change relativeRingRestriction f J (U := V) le_rfl r = r at he
  rw [he]

/-- Constants in the ambient tensor ring act through the original chart restriction. -/
lemma chartTensorModule_algebraMap_smul (U : X.affineOpens) (h : U.1 ≤ V.1)
    (r : Γ(X, V.1)) (s : chartModule f J M V U h) :
    let _ := chartAlgebra f V
    let _ := chartTensorModule f J M V U h
    algebraMap Γ(X, V.1) (Γ(X, V.1) ⊗[R] reesAlgebra J) r • s = r • s := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  let _ := Rees.relativeModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J
  let _ := chartTensorModule f J M V U h
  have he := RingHom.congr_fun (relativeRingRestriction_left f J h) r
  change relativeRingRestriction f J h
      (algebraMap Γ(X, V.1) (Γ(X, V.1) ⊗[R] reesAlgebra J) r) =
    algebraMap Γ(X, U.1) (Γ(X, U.1) ⊗[R] reesAlgebra J)
      (X.presheaf.map (homOfLE h).op r) at he
  change (relativeRingRestriction f J h
    (algebraMap Γ(X, V.1) (Γ(X, V.1) ⊗[R] reesAlgebra J) r)) •
      (show Rees.extendedModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J from s) = _
  rw [he, Rees.relativeModule_algebraMap_smul]
  rfl

/-- The fixed tensor-ring action extends the original fixed-chart action. -/
instance chartTensorModule_scalarTower (U : X.affineOpens) (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartTensorModule f J M V U h
    IsScalarTower Γ(X, V.1) (Γ(X, V.1) ⊗[R] reesAlgebra J)
      (chartModule f J M V U h) := by
  let _ := chartAlgebra f V
  let _ := chartTensorModule f J M V U h
  exact IsScalarTower.of_algebraMap_smul (chartTensorModule_algebraMap_smul f J M V U h)

/-- Actual polynomial restrictions are linear over the larger relative tensor ring. -/
def chartTensorRestriction {U W : X.affineOpens}
    (hU : U.1 ≤ V.1) (hW : W.1 ≤ V.1) (h : U.1 ≤ W.1) :
    let _ := chartAlgebra f V
    let _ := chartTensorModule f J M V W hW
    let _ := chartTensorModule f J M V U hU
    chartModule f J M V W hW →ₗ[Γ(X, V.1) ⊗[R] reesAlgebra J]
      chartModule f J M V U hU := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f W
  let _ := chartAlgebra f U
  let _ := Rees.relativeModule (S := Γ(X, W.1)) (M := Γ(M, W.1)) J
  let _ := Rees.relativeModule (S := Γ(X, U.1)) (M := Γ(M, U.1)) J
  let _ := chartTensorModule f J M V W hW
  let _ := chartTensorModule f J M V U hU
  refine { toFun := relativeRestriction f J M h, map_add' := map_add _, map_smul' := ?_ }
  intro r s
  change relativeRestriction f J M h ((relativeRingRestriction f J hW r) •
    (show Rees.extendedModule (S := Γ(X, W.1)) (M := Γ(M, W.1)) J from s)) = _
  rw [map_smulₛₗ]
  exact congrArg (fun t ↦ t • relativeRestriction f J M h s)
    (AlgHom.congr_fun (relativeRingRestriction_comp f J h hW) r)

end FLT.Mazur.BaseAdicRees
