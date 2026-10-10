/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafCoordinateNaturality
public import FLT.Mazur.SchemeAffineAmbientTestCocycle
public import FLT.Mazur.SchemeAffineSchemeTestNaturality

/-!
# Naturality of ambient chart comparisons

Coordinate naturality transports the scheme-test square to the ambient
pushforwards of the descended affine chart modules.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open ModuleSheafOverlapImageTransition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M N : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (E : SchemeGeometricDescent.Data p N)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [((pullback C.cover).obj N).IsQuasicoherent]
variable [((pullback C'.cover).obj N).IsQuasicoherent]
variable [IsOpenImmersion C.base] [IsOpenImmersion C'.base]
attribute [local irreducible] sheaf map schemeTestComparison

/-- Ambient comparison commutes with the pushforwards of compatible chart maps. -/
@[reassoc]
theorem ambientTestComparison_naturality (a : W ⟶ X)
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a)
    (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (pullback a).map ((pushforward C.base).map (C.map D E f hf)) ≫
        C.ambientTestComparison C' E a i j hi hj =
      C.ambientTestComparison C' D a i j hi hj ≫
        (pullback a).map ((pushforward C'.base).map (C'.map D E f hf)) := by
  simp only [ambientTestComparison, Category.assoc]
  rw [coordinateIso_naturality_assoc, schemeTestComparison_naturality_assoc,
    coordinateIso_inv_naturality]

end FLT.Mazur.SchemeAffineDescent.Chart
