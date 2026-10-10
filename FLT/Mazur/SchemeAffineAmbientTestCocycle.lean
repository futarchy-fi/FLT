/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSchemeTestCocycle
public import FLT.Mazur.ModuleSheafOverlapImageTransition

/-!
# Ambient chart-pushforward cocycles

For open base charts, coordinate conjugation expresses the actual glued
comparison between pullbacks of ambient chart pushforwards and preserves its cocycle.
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
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [IsOpenImmersion C.base] [IsOpenImmersion C'.base]
attribute [local irreducible] sheaf schemeTestComparison

/-- Compare the ambient chart pushforwards on a common scheme test. -/
def ambientTestComparison (a : W ⟶ X)
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a) :
    (pullback a).obj ((pushforward C.base).obj (C.sheaf D)) ⟶
      (pullback a).obj ((pushforward C'.base).obj (C'.sheaf D)) :=
  (coordinateIso i C.base a hi (C.sheaf D)).hom ≫
    C.schemeTestComparison C' D i j (hi.trans hj.symm) ≫
      (coordinateIso j C'.base a hj (C'.sheaf D)).inv

/-- The ambient test comparison is invertible. -/
instance ambientTestComparison_isIso (a : W ⟶ X)
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a) :
    IsIso (C.ambientTestComparison C' D a i j hi hj) := by
  unfold ambientTestComparison
  infer_instance

/-- Coordinate conjugation preserves the global cocycle for ambient chart sheaves. -/
theorem ambientTestComparison_cocycle (T : Fin 3 → Chart p)
    (a : W ⟶ X) (b : ∀ i, W ⟶ Spec (T i).baseRing)
    (h : ∀ i, b i ≫ (T i).base = a)
    [∀ i, ((pullback (T i).cover).obj M).IsQuasicoherent]
    [∀ i, IsOpenImmersion (T i).base] :
    (T 0).ambientTestComparison (T 1) D a (b 0) (b 1) (h 0) (h 1) ≫
      (T 1).ambientTestComparison (T 2) D a (b 1) (b 2) (h 1) (h 2) =
      (T 0).ambientTestComparison (T 2) D a (b 0) (b 2) (h 0) (h 2) := by
  simp only [ambientTestComparison, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((T 0).schemeTestComparison (T 1) D _ _ _),
    schemeTestComparison_cocycle D T a b h]

end FLT.Mazur.SchemeAffineDescent.Chart
