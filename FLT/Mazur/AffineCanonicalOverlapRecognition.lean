/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOverlapUnitDetection
public import FLT.Mazur.SchemePullbackOverlap

/-!
# Coaction compatibility is the canonical geometric overlap equation

The affine tensor criterion and actual pullback path comparison agree.
A reconstruction chart is coaction-compatible exactly when its specified
overlap is the canonical geometric overlap transported through that chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescentRecognition
open AffineGeometricDescent AffineGeometricOverlap AffineOverlapTensor
open AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemePullbackOverlap.chartOverlap
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable (A : (Spec R).Modules) [A.IsQuasicoherent]
variable {M : (Spec S).Modules} [M.IsQuasicoherent]
variable (D : Data φ M) (e : (pullback (Spec.map φ)).obj A ≅ M)

/-- Coaction compatibility is equality with the actual canonical reconstruction overlap. -/
theorem coactionCompatible_iff_canonical_overlap :
    let := φ.hom.toAlgebra
    ∀ (k : Spec (.of (S ⊗[R] S)) ⟶ Spec R)
      (hl : Spec.map (CommRingCat.ofHom (left R S)) ≫ Spec.map φ = k)
      (hr : Spec.map (CommRingCat.ofHom (right R S)) ≫ Spec.map φ = k),
    CoactionCompatible φ A D e ↔ D.val =
      SchemePullbackOverlap.chartOverlap (Spec.map φ)
        (Spec.map (CommRingCat.ofHom (left R S)))
        (Spec.map (CommRingCat.ofHom (right R S))) k hl hr A e := by
  let := φ.hom.toAlgebra
  intro _ k hl hr
  constructor
  · intro h
    apply overlap_eq_of_section_units φ A e
    intro m
    have hd := (coactionCompatible_iff_overlap_unit φ D A e).mp h m
    have hc := SchemePullbackOverlap.chartOverlap_unit (Spec.map φ)
      (Spec.map (CommRingCat.ofHom (left R S)))
      (Spec.map (CommRingCat.ofHom (right R S))) k hl hr A e m
    exact hd.trans hc.symm
  · intro h
    apply (coactionCompatible_iff_overlap_unit φ D A e).mpr
    intro m
    rw [h]
    exact SchemePullbackOverlap.chartOverlap_unit (Spec.map φ)
      (Spec.map (CommRingCat.ofHom (left R S)))
      (Spec.map (CommRingCat.ofHom (right R S))) k hl hr A e m

/-- The tensor-constructed chart datum has exactly the canonical geometric overlap. -/
theorem chartData_val_eq_canonical_overlap :
    let := φ.hom.toAlgebra
    ∀ (k : Spec (.of (S ⊗[R] S)) ⟶ Spec R)
      (hl : Spec.map (CommRingCat.ofHom (left R S)) ≫ Spec.map φ = k)
      (hr : Spec.map (CommRingCat.ofHom (right R S)) ≫ Spec.map φ = k),
    (chartData φ A e).val =
      SchemePullbackOverlap.chartOverlap (Spec.map φ)
        (Spec.map (CommRingCat.ofHom (left R S)))
        (Spec.map (CommRingCat.ofHom (right R S))) k hl hr A e := by
  let := φ.hom.toAlgebra
  intro _ k hl hr
  exact (coactionCompatible_iff_canonical_overlap φ A (chartData φ A e) e k hl hr).mp
    (chartData_compatible φ A e)

end FLT.Mazur.AffineGeometricDescentRecognition
