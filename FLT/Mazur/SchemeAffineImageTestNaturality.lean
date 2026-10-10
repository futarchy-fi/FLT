/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineAmbientTestNaturality
public import FLT.Mazur.SchemeAffineImageTestComparison
public import FLT.Mazur.ModuleSheafLocalNaturality

/-!
# Naturality of image-open comparisons

Extension from pullbacks to image opens preserves the ambient naturality
square. Its sealed evaluation retains the original chart maps on sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open ModuleSheafOpenImmersionLocalHom ModuleSheafMorphismGluing
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
attribute [local irreducible] sheaf map ambientTestComparison

/-- Compatible original maps commute with the actual image-open comparison. -/
@[reassoc]
theorem imageTestComparison_naturality (a : W ⟶ X) [IsOpenImmersion a]
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a)
    (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (((pushforward C.base).map (C.map D E f hf)).over a.opensRange) ≫
        C.imageTestComparison C' E a i j hi hj =
      C.imageTestComparison C' D a i j hi hj ≫
        (((pushforward C'.base).map (C'.map D E f hf)).over a.opensRange) := by
  have h := congrArg (localHom a)
    (C.ambientTestComparison_naturality C' D E a i j hi hj f hf)
  simpa only [localHom_comp, localHom_map, imageTestComparison] using h

/-- The image comparison square holds on every subopen using sealed evaluation. -/
theorem imageTestComparison_naturality_eval (a : W ⟶ X) [IsOpenImmersion a]
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a)
    (f : M ⟶ N) (hf : D.MapCompatible p E f)
    (V : X.Opens) (hV : V ≤ a.opensRange)
    (s : Γ((pushforward C.base).obj (C.sheaf D), V)) :
    localEval (C.imageTestComparison C' E a i j hi hj) hV
        (((pushforward C.base).map (C.map D E f hf)).app V s) =
      ((pushforward C'.base).map (C'.map D E f hf)).app V
        (localEval (C.imageTestComparison C' D a i j hi hj) hV s) :=
  localEval_naturality hV _ _ _ _
    (C.imageTestComparison_naturality C' D E a i j hi hj f hf) s

end FLT.Mazur.SchemeAffineDescent.Chart
